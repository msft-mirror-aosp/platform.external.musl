/*
 * Copyright (C) 2021 The Android Open Source Project
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <link.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/param.h>
#include <sys/syscall.h>
#include <sys/user.h>
#include <unistd.h>

typedef void EntryFunc(void);

long ri_syscall(long syscall, ...);
void _start(void);
static EntryFunc* ri_main(void* raw_args) __attribute__((used));

#define PAGE_START(x) ((x) & PAGE_MASK)
#define PAGE_END(x) PAGE_START((x) + (PAGE_SIZE - 1))
#define NT_TYPE_RELINTERP 5
#define ROUND_UP(x, y) (((x) + (y) - 1) / (y) * (y))
#define NOTE_SECTION_NAME ".note.google.relinterp"

// The stack pointer should be 16-byte-aligned at the first instruction of the entry point.
//
// This entry point can be invoke between relocating the executable and transferring control to the
// real entry point (e.g. if the user invokes the loader directly, but also in the normal use case).
// Save and restore arguments from the loader to the entry point.
asm(
  ".globl __relinterp_start\n"
  "__relinterp_start:\n"
  // TODO: annotate with cfi (do we need to stop unwinding at this frame?)
  "  push %rbp\n"
  "  mov %rsp, %rbp\n"
  "  sub $0x38, %rsp\n"
  "  mov %rdi, 0x0(%rsp)\n"
  "  mov %rsi, 0x8(%rsp)\n"
  "  mov %rdx, 0x10(%rsp)\n"
  "  mov %rcx, 0x18(%rsp)\n"
  "  mov %r8, 0x20(%rsp)\n"
  "  mov %r9, 0x28(%rsp)\n"
  "  lea 0x8(%rbp), %rdi\n"
  // The stack pointer should be 16-byte aligned before this call instruction.
  // TODO: it might be better to realign the stack here rather than assume the caller/kernel did it right.
  "  call ri_main\n"
  "  mov 0x0(%rsp), %rdi\n"
  "  mov 0x8(%rsp), %rsi\n"
  "  mov 0x10(%rsp), %rdx\n"
  "  mov 0x18(%rsp), %rcx\n"
  "  mov 0x20(%rsp), %r8\n"
  "  mov 0x28(%rsp), %r9\n"
  "  mov %rbp, %rsp\n"
  "  pop %rbp\n"
  "  jmp *%rax\n"
);

asm(
  "ri_syscall:\n"
  "  mov %edi, %eax\n"
  "  mov %rsi, %rdi\n"
  "  mov %rdx, %rsi\n"
  "  mov %rcx, %rdx\n"
  "  mov %r8,  %r10\n"
  "  mov %r9,  %r8\n"
  "  mov 8(%rsp), %r9\n"
  "  syscall\n"
  "  cmpq $-4095, %rax\n"
  "  jb 1f\n"
  "  negl %eax\n"
  "  movl %eax, %edi\n"
  "  call ri_set_errno\n"
  "1:\n"
  "  ret\n"
);

// With lld, these variables should be output into .rodata and placed into the first PT_LOAD
// segment.
static const ElfW(Phdr) kVirtualTable[64];
static const char kVirtualInterp[PATH_MAX];

// Ensure that this file's executable code is in a different page from the virtual table above, if
// the executable uses an initial read-exec PT_LOAD.
asm(".space 4096");

static bool g_debug = false;
static const char* g_prog_name = NULL;
static int g_errno = 0;

__attribute__((visibility("hidden"))) extern ElfW(Dyn) _DYNAMIC[];

__attribute__((used))
static long ri_set_errno(int val) {
  g_errno = val;
  return -1;
}

static ssize_t ri_write(int fd, const void* buf, size_t amt) {
  return ri_syscall(SYS_write, fd, buf, amt);
}

__attribute__((noreturn))
static void ri_exit(int status) {
  ri_syscall(SYS_exit, status);
  __builtin_unreachable();
}

static int ri_open(const char* path, int flags, mode_t mode) {
  return ri_syscall(SYS_open, path, flags, mode);
}

static int ri_close(int fd) {
  return ri_syscall(SYS_close, fd);
}

static off_t ri_lseek(int fd, off_t offset, int whence) {
  return ri_syscall(SYS_lseek, fd, offset, whence);
}

static ssize_t ri_readlink(const char* path, char* buf, size_t size) {
  return ri_syscall(SYS_readlinkat, AT_FDCWD, path, buf, size);
}

static void* ri_mmap(void* addr, size_t length, int prot, int flags, int fd, off_t offset) {
  return (void*)ri_syscall(SYS_mmap, addr, length, prot, flags, fd, offset);
}

static void* ri_munmap(void* addr, size_t length) {
  return (void*)ri_syscall(SYS_munmap, addr, length);
}

static int ri_mprotect(void* addr, size_t len, int prot) {
  return ri_syscall(SYS_mprotect, addr, len, prot);
}

static size_t ri_strlen(const char* src) {
  for (size_t len = 0;; ++len) {
    if (src[len] == '\0') return len;
  }
}

static char* ri_strcpy(char* dst, const char* src) {
  char* result = dst;
  while ((*dst = *src) != '\0') {
    ++dst;
    ++src;
  }
  return result;
}

static char* ri_strcat(char* dst, const char* src) {
  ri_strcpy(dst + ri_strlen(dst), src);
  return dst;
}

static void* ri_memset(void* dst, int val, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    ((char*)dst)[i] = val;
  }
  return dst;
}

__attribute__ ((unused))
static void* ri_memcpy(void* dst, const void* src, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    ((char*)dst)[i] = ((char*)src)[i];
  }
  return dst;
}

static int ri_strncmp(const char* x, const char *y, size_t maxlen) {
  for (size_t i = 0;; ++i) {
    if (i == maxlen) return 0;
    int result = (unsigned char)x[i] - (unsigned char)y[i];
    if (result != 0) return result;
    if (x[i] == '\0') return 0;
  }
}

static int ri_strcmp(const char* x, const char *y) {
  return ri_strncmp(x, y, SIZE_MAX);
}

static char* ri_strrchr(const char* str, int ch) {
  char* result = NULL;
  while (true) {
    if (*str == ch) result = (char*)str;
    if (*str == '\0') break;
    ++str;
  }
  return result;
}

static void ri_dirname(char* path) {
  char* last_slash = ri_strrchr(path, '/');
  if (last_slash > path) *last_slash = '\0';
}

static void out_str_n(const char* str, size_t n) {
  ri_write(STDERR_FILENO, str, n);
}

static void out_str(const char* str) {
  out_str_n(str, ri_strlen(str));
}

static char* ul_to_str(unsigned long i, char* out, unsigned char base) {
  char buf[65];
  char* cur = &buf[65];
  *--cur = '\0';
  do {
    *--cur = "0123456789abcdef"[i % base];
    i /= base;
  } while (i > 0);
  return ri_strcpy(out, cur);
}

static char* l_to_str(long i, char* out, unsigned char base) {
  if (i < 0) {
    *out = '-';
    ul_to_str(-(unsigned long)i, out + 1, base);
    return out;
  } else {
    return ul_to_str(i, out, base);
  }
}

static const char* ri_strerror(int err) {
  switch (err) {
    case EPERM: return "Operation not permitted";
    case ENOENT: return "No such file or directory";
    case EIO: return "I/O error";
    case ENXIO: return "No such device or address";
    case EAGAIN: return "Try again";
    case ENOMEM: return "Out of memory";
    case EACCES: return "Permission denied";
    case ENODEV: return "No such device";
    case ENOTDIR: return "Not a directory";
    case EINVAL: return "Invalid argument";
    case ENFILE: return "File table overflow";
    case EMFILE: return "Too many open files";
    case ESPIPE: return "Illegal seek";
    case ENAMETOOLONG: return "File name too long";
    case ELOOP: return "Too many symbolic links encountered";
  }
  static char buf[64];
  ri_strcpy(buf, "Unknown error ");
  l_to_str(err, buf + ri_strlen(buf), 10);
  return buf;
}

static void outv(const char *fmt, va_list ap) {
  char buf[65];
  while (true) {
    if (fmt[0] == '\0') break;

#define NUM_FMT(num_fmt, type, func, base)                  \
    if (!ri_strncmp(fmt, num_fmt, sizeof(num_fmt) - 1)) {   \
      out_str(func(va_arg(ap, type), buf, base));           \
      fmt += sizeof(num_fmt) - 1;                           \
      continue;                                             \
    }
    NUM_FMT("%d",  int,           l_to_str,  10);
    NUM_FMT("%ld", long,          l_to_str,  10);
    NUM_FMT("%u",  unsigned int,  ul_to_str, 10);
    NUM_FMT("%lu", unsigned long, ul_to_str, 10);
    NUM_FMT("%zu", size_t,        ul_to_str, 10);
    NUM_FMT("%x",  unsigned int,  ul_to_str, 16);
    NUM_FMT("%lx", unsigned long, ul_to_str, 16);
    NUM_FMT("%zx", size_t,        ul_to_str, 16);
#undef NUM_FMT

    if (!ri_strncmp(fmt, "%p", 2)) {
      out_str(ul_to_str((unsigned long)va_arg(ap, void*), buf, 16));
      fmt += 2;
    } else if (!ri_strncmp(fmt, "%s", 2)) {
      const char* arg = va_arg(ap, const char*);
      out_str(arg ? arg : "(null)");
      fmt += 2;
    } else if (!ri_strncmp(fmt, "%%", 2)) {
      out_str("%");
      fmt += 2;
    } else if (fmt[0] == '%') {
      buf[0] = fmt[1];
      buf[1] = '\0';
      out_str("relinterp error: unrecognized output specifier: '%");
      out_str(buf);
      out_str("'\n");
      ri_exit(1);
    } else {
      size_t len = 0;
      while (fmt[len] != '\0' && fmt[len] != '%') ++len;
      out_str_n(fmt, len);
      fmt += len;
    }
  }
}

__attribute__((format(printf, 1, 2)))
static void debug(const char* fmt, ...) {
  if (!g_debug) return;
  out_str("relinterp: ");

  va_list ap;
  va_start(ap, fmt);
  outv(fmt, ap);
  va_end(ap);
  out_str("\n");
}

__attribute__((format(printf, 1, 2), noreturn))
static void fatal(const char* fmt, ...) {
  out_str("relinterp: ");
  if (g_prog_name) {
    out_str(g_prog_name);
    out_str(": ");
  }
  out_str("fatal error: ");

  va_list ap;
  va_start(ap, fmt);
  outv(fmt, ap);
  va_end(ap);
  out_str("\n");
  ri_exit(1);
}

static void* optimizer_barrier(void* val) {
  __asm__ volatile ("nop" :: "r"(&val) : "memory");
  return val;
}

typedef struct {
  unsigned long key;
  unsigned long value;
} AuxEntry;

typedef struct {
  int argc;
  char **argv;
  char **envp;
  size_t envp_count;
  AuxEntry* auxv;
  size_t auxv_count;
} KernelArguments;

static KernelArguments read_args(void* raw_args) {
  KernelArguments result;
  result.argc = *(long*)raw_args;
  result.argv = (char**)((void**)raw_args + 1);
  result.envp = result.argv + result.argc + 1;

  char** envp = result.envp;
  while (*envp != NULL) ++envp;
  result.envp_count = envp - result.envp;
  ++envp;

  result.auxv = (AuxEntry*)envp;
  size_t count = 0;
  while (result.auxv[count].key != 0) {
    ++count;
  }
  result.auxv_count = count;
  return result;
}

static void dump_auxv(const KernelArguments* args) {
  for (size_t i = 0; i < args->auxv_count; ++i) {
    const char* name = "";
    switch (args->auxv[i].key) {
      case AT_BASE: name = " [AT_BASE]"; break;
      case AT_PHDR: name = " [AT_PHDR]"; break;
      case AT_PHENT: name = " [AT_PHENT]"; break;
      case AT_PHNUM: name = " [AT_PHNUM]"; break;
      case AT_ENTRY: name = " [AT_ENTRY]"; break;
      case AT_SYSINFO: name = " [AT_SYSINFO]"; break;
      case AT_SYSINFO_EHDR: name = " [AT_SYSINFO_EHDR]"; break;
    }
    debug("  %lu => 0x%lx%s", args->auxv[i].key, args->auxv[i].value, name);
  }
}

static unsigned long ri_getauxval(const KernelArguments* args, unsigned long kind,
                                  bool allow_missing) {
  for (size_t i = 0; i < args->auxv_count; ++i) {
    if (args->auxv[i].key == kind) return args->auxv[i].value;
  }
  if (!allow_missing) fatal("could not find aux vector entry %lu", kind);
  return 0;
}

static int elf_flags_to_prot(int flags) {
  int result = 0;
  if (flags & PF_R) result |= PROT_READ;
  if (flags & PF_W) result |= PROT_WRITE;
  if (flags & PF_X) result |= PROT_EXEC;
  return result;
}

typedef struct {
  int fd;
  char path[PATH_MAX];
} OpenedLoader;

typedef struct {
  void* base_addr;
  EntryFunc* entry;
} LoadedInterp;

static LoadedInterp load_interp(const OpenedLoader *loader, ElfW(Ehdr)* hdr) {
  ElfW(Phdr)* phdr = (ElfW(Phdr)*)((char*)hdr + hdr->e_phoff);
  size_t phdr_count = hdr->e_phnum;

  size_t max_vaddr = 0;

  // Find the virtual address extent.
  for (size_t i = 0; i < phdr_count; ++i) {
    if (phdr[i].p_type == PT_LOAD) {
      max_vaddr = PAGE_END(MAX(max_vaddr, phdr[i].p_vaddr + phdr[i].p_memsz));
    }
  }

  // Map an area to fit the loader.
  void* loader_vaddr = ri_mmap(NULL, max_vaddr, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (loader_vaddr == (void*)MAP_FAILED) {
    fatal("reservation mmap of 0x%zx bytes for %s failed: %s", max_vaddr, loader->path,
          ri_strerror(g_errno));
  }

  // Map each PT_LOAD.
  for (size_t i = 0; i < phdr_count; ++i) {
    if (phdr[i].p_type == PT_LOAD) {
      size_t start = PAGE_START(phdr[i].p_vaddr);
      const size_t end = PAGE_END(phdr[i].p_vaddr + phdr[i].p_memsz);
      if (phdr[i].p_filesz > 0) {
        const size_t file_end = phdr[i].p_vaddr + phdr[i].p_filesz;
        void* tmp = ri_mmap((char*)loader_vaddr + start,
                            file_end - start,
                            elf_flags_to_prot(phdr[i].p_flags),
                            MAP_PRIVATE | MAP_FIXED, loader->fd, PAGE_START(phdr[i].p_offset));
        if (tmp == (void*)MAP_FAILED) {
          fatal("PT_LOAD mmap failed (%s segment #%zu): %s", loader->path, i,
                ri_strerror(g_errno));
        }
        start = file_end;
        if (phdr[i].p_flags & PF_W) {
          // The bytes between p_filesz and PAGE_END(p_filesz) currently come from the file mapping,
          // but they need to be zeroed. (Apparently this zeroing isn't necessary if the segment isn't
          // writable, and zeroing a non-writable page would be inconvenient.)
          ri_memset((char*)loader_vaddr + start, '\0', PAGE_END(start) - start);
        }
        start = PAGE_END(start);
      }
      if (start < end) {
        // The memory is already zeroed, because it comes from an anonymous file mapping. Just set
        // the protections correctly.
        int result = ri_mprotect((char*)loader_vaddr + start, end - start,
                                 elf_flags_to_prot(phdr[i].p_flags));
        if (result != 0) {
          fatal("mprotect of PT_LOAD failed (%s segment #%zu): %s", loader->path, i,
                ri_strerror(g_errno));
        }
      }
    }
  }

  return (LoadedInterp) {
    .base_addr = loader_vaddr,
    .entry = (EntryFunc*)((uintptr_t)loader_vaddr + hdr->e_entry),
  };
}

typedef struct {
  ElfW(Phdr)* phdr;
  size_t phdr_count;
  uintptr_t load_bias;
  ElfW(Ehdr)* ehdr;
  ElfW(Phdr)* first_load;
} ExeInfo;

static ExeInfo get_exe_info(const KernelArguments* args) {
  ExeInfo result = { 0 };
  result.phdr = (ElfW(Phdr)*)ri_getauxval(args, AT_PHDR, false);
  result.phdr_count = ri_getauxval(args, AT_PHNUM, false);

  debug("orig phdr     = %p", (void*)result.phdr);
  debug("orig phnum    = %zu", result.phdr_count);

  for (size_t i = 0; i < result.phdr_count; ++i) {
    if (result.phdr[i].p_type == PT_DYNAMIC) {
      result.load_bias = (uintptr_t)&_DYNAMIC - result.phdr[i].p_vaddr;
    }
  }
  debug("load_bias     = 0x%lx", (unsigned long)result.load_bias);

  for (size_t i = 0; i < result.phdr_count; ++i) {
    ElfW(Phdr)* phdr = &result.phdr[i];
    if (phdr->p_type != PT_LOAD) continue;
    result.first_load = phdr;
    if (phdr->p_offset != 0) {
      fatal("expected zero p_offset for first PT_LOAD, found 0x%zx instead",
            (size_t)phdr->p_offset);
    }
    result.ehdr = (ElfW(Ehdr)*)(phdr->p_vaddr + result.load_bias);
    break;
  }
  debug("ehdr          = %p", (void*)result.ehdr);

  return result;
}

// Loaders typically read the PT_INTERP of the executable, e.g. to set a pathname on the loader.
// glibc insists on the executable having PT_INTERP, and aborts if it's missing.  Musl passes it
// to debuggers to find symbols for the loader, which includes all the libc symbols.

// Make a copy of the phdr table and insert PT_INTERP into the copy.
// Make the variable's const so that they will be located in the initial readable PT_LOAD segment,
// which guarantees that their vaddrs and file offsets will be the same. (There is only a single
// ElfW(Ehdr)::e_phoff field that loaders seem to interpret as both a vaddr and a file offset.)
//
// TODO: If it's kept, then maybe we can remove the read-only/mprotect stuff if file offsets don't
// matter (e.g. maybe ElfW(Ehdr)::e_phoff is ignored, and maybe ElfW(Phdr)::p_offset is effectively
// a virtual address offset to the ELF header instead).

static void insert_pt_interp_into_phdr_table(const KernelArguments* args, const ExeInfo* exe,
                                             const char* loader_realpath) {
  uintptr_t remap_start = PAGE_START((uintptr_t)exe->ehdr);
  uintptr_t remap_end = PAGE_END(MAX(
    (uintptr_t)(&kVirtualTable + 1),
    (uintptr_t)(&kVirtualInterp + 1)));

  debug("remap_start   = 0x%lx", remap_start);
  debug("remap_end     = 0x%lx", remap_end);

  uintptr_t first_load_start = exe->load_bias + exe->first_load->p_vaddr;
  uintptr_t first_load_end = first_load_start + exe->first_load->p_memsz;
  first_load_start = PAGE_START(first_load_start);
  first_load_end = PAGE_END(first_load_end);
  if (remap_start < first_load_start || remap_end > first_load_end) {
    fatal("virtual phdr table not contained within first PT_LOAD segment (0x%zx, 0x%zx)",
          (size_t)first_load_start, (size_t)first_load_end);
  }

  if (ri_mprotect((void*)remap_start,
                  remap_end - remap_start,
                  PROT_READ | PROT_WRITE) != 0) {
    fatal("could not make executable's ELF header writable: %s", ri_strerror(g_errno));
  }

  // Reserve extra space for the inserted PT_INTERP segment and a null terminator.
  if (exe->phdr_count + 2 > sizeof(kVirtualTable) / sizeof(kVirtualTable[0])) {
    fatal("too many phdr table entries in executable");
  }

  ElfW(Phdr*) cur = (ElfW(Phdr)*)optimizer_barrier((void*)kVirtualTable);
  for (size_t i = 0; i < exe->phdr_count; ++i) {
    *cur = exe->phdr[i];
    if (cur->p_type == 0) fatal("unexpected null phdr entry at index %zu", i);
    if (cur->p_type == PT_PHDR) {
      cur->p_offset = (uintptr_t)&kVirtualTable - (uintptr_t)exe->ehdr;
      cur->p_vaddr = (uintptr_t)&kVirtualTable - exe->load_bias;
      cur->p_paddr = cur->p_vaddr;
      cur->p_memsz = (exe->phdr_count + 1) * sizeof(ElfW(Phdr));
      cur->p_filesz = cur->p_memsz;
    }
    ++cur;
  }

  // Insert PT_INTERP at the end.
  cur->p_type = PT_INTERP;
  cur->p_offset = (uintptr_t)&kVirtualInterp - (uintptr_t)exe->ehdr;
  cur->p_vaddr = (uintptr_t)&kVirtualInterp - exe->load_bias;
  cur->p_paddr = cur->p_vaddr;
  cur->p_filesz = ri_strlen(kVirtualInterp) + 1;
  cur->p_memsz = ri_strlen(kVirtualInterp) + 1;
  cur->p_flags = PF_R;
  cur->p_align = 1;
  ++cur;

  ri_strcpy((char*)optimizer_barrier((void*)kVirtualInterp), loader_realpath);

  // Updating these ehdr fields seems to be unnecessary in practice, because libcs instead use
  // AT_PHDR and AT_PHNUM to find the phdr table. This is easy to do, though.
  exe->ehdr->e_phoff = (uintptr_t)&kVirtualTable - (uintptr_t)exe->ehdr;
  exe->ehdr->e_phnum = exe->phdr_count + 1;
  debug("new phdr      = %p", (void*)&kVirtualTable);
  debug("new phnum     = %zu", (exe->phdr_count + 1));

  if (ri_mprotect(
        (void*)remap_start,
        remap_end - remap_start,
        elf_flags_to_prot(exe->first_load->p_flags)) != 0) {
    fatal("could not make executable's ELF header read-only again: %s", ri_strerror(g_errno));
  }

  // Update the aux vector with the new phdr+phnum.
  for (size_t i = 0; i < args->auxv_count; ++i) {
    if (args->auxv[i].key == AT_PHDR) {
      args->auxv[i].value = (unsigned long)&kVirtualTable;
    } else if (args->auxv[i].key == AT_PHNUM) {
      args->auxv[i].value = exe->phdr_count + 1;
    }
  }
}

static const char* read_relinterp_note(const ExeInfo* exe) {
  for (size_t i = 0; i < exe->phdr_count; ++i) {
    ElfW(Phdr)* const phdr = &exe->phdr[i];
    if (phdr->p_type == PT_NOTE) {
      char* note_c = (char*)(phdr->p_vaddr + exe->load_bias);
      char* const end = note_c + phdr->p_memsz;
      while (note_c < end && end - note_c >= sizeof(ElfW(Nhdr))) {
        ElfW(Nhdr)* const note = (ElfW(Nhdr)*)note_c;
        const size_t total_note_size = sizeof(ElfW(Nhdr)) +
          ROUND_UP(note->n_namesz, 4) +
          ROUND_UP(note->n_descsz, 4);
        if (end - note_c < total_note_size) break;
        if (note->n_namesz == sizeof("Google") &&
            !ri_strcmp((char*)(note + 1), "Google") &&
            note->n_type == NT_TYPE_RELINTERP) {
          char* result = (char*)(note + 1) + ROUND_UP(note->n_namesz, 4);
          debug("%s path is '%s'", NOTE_SECTION_NAME, result);
          return result;
        }
        note_c += total_note_size;
      }
    }
  }
  fatal("error: could not find " NOTE_SECTION_NAME " note");
}

static void realpath_fd(int fd, const char* orig_path, char* out, size_t len) {
  char path[64];
  ri_strcpy(path, "/proc/self/fd/");
  ul_to_str(fd, path + ri_strlen(path), 10);
  ssize_t result = ri_readlink(path, out, len);
  if (result == -1) fatal("could not get realpath of %s: %s", orig_path, ri_strerror(g_errno));
  if ((size_t)result >= len) fatal("realpath of %s too long", orig_path);
}

static OpenedLoader open_loader(const ExeInfo* exe) {
  const char* loader_rel_path = read_relinterp_note(exe);
  char tmp[PATH_MAX];

  if (loader_rel_path[0] == '/') {
    tmp[0] = '\0';
  } else {
    // If /proc isn't mounted, this error will be visible to an end user.
    ssize_t len = ri_readlink("/proc/self/exe", tmp, sizeof(tmp));
    if (len <= 0 || (size_t)len >= sizeof(tmp)) {
      fatal("could not readlink /proc/self/exe: %s", ri_strerror(g_errno));
    }
    tmp[len] = '\0';

    ri_dirname(tmp);
    ri_strcat(tmp, "/");
  }

  OpenedLoader result;
  if (ri_strlen(tmp) + ri_strlen(loader_rel_path) + 1 > sizeof(tmp)) {
    fatal("path to loader exceeds PATH_MAX: %s%s", tmp, loader_rel_path);
  }

  ri_strcat(tmp, loader_rel_path);

  debug("trying to open '%s'", tmp);
  result.fd = ri_open(tmp, O_RDONLY, 0);
  if (result.fd < 0) fatal("could not open loader %s: %s", tmp, ri_strerror(g_errno));

  realpath_fd(result.fd, tmp, result.path, sizeof(result.path));
  return result;
}

// Use a trick to determine whether the executable has been relocated yet. This variable points to
// a variable in libc. It will be NULL if and only if the program hasn't been linked yet. This
// should accommodate these situations:
//  - The program was actually statically-linked instead.
//  - Either a PIE or non-PIE dynamic executable.
//  - Any situation where the loader calls the executable's _start:
//     - In normal operation, the kernel calls the executable's _start, _start jumps to the loader's
//       entry point, which jumps to _start again after linking it.
//     - The executable actually has its PT_INTERP set after all.
//     - The user runs the loader, passing it the path of the executable.
// This C file must always be compiled as PIC, or else the linker will use a COPY relocation and
// duplicate "environ" into the executable.
static bool is_exe_relocated(void) {
  // Use the GOT to get the address of environ.
  extern char** environ;
  void* read_environ = optimizer_barrier(&environ);
  debug("read_environ = %p", read_environ);
  return read_environ != NULL;
}

static EntryFunc* ri_main(void* raw_args) {
  const KernelArguments args = read_args(raw_args);
  for (size_t i = 0; i < args.envp_count; ++i) {
    if (!ri_strcmp(args.envp[i], "RELINTERP_DEBUG=1")) {
      g_debug = true;
    }
  }
  if (args.argc >= 1) {
    g_prog_name = args.argv[0];
  }

  if (is_exe_relocated()) {
    debug("ri_main: exe is already relocated, jumping to _start");
    return _start;
  }

  debug("entering ri_main");

  const ExeInfo exe = get_exe_info(&args);
  OpenedLoader loader = open_loader(&exe);
  off_t len = ri_lseek(loader.fd, 0, SEEK_END);
  if (len == (off_t)-1) fatal("lseek on %s failed: %s", loader.path, ri_strerror(g_errno));

  void* loader_data = ri_mmap(NULL, len, PROT_READ, MAP_PRIVATE, loader.fd, 0);
  if (loader_data == (void*)MAP_FAILED) {
    fatal("could not mmap %s: %s", loader.path, ri_strerror(g_errno));
  }

  LoadedInterp interp = load_interp(&loader, (ElfW(Ehdr)*)loader_data);
  if (ri_munmap(loader_data, len) != 0) fatal("munmap failed: %s", ri_strerror(g_errno));

  debug("original auxv:");
  dump_auxv(&args);

  // Create a virtual phdr table that includes PT_INTERP, for the benefit of loaders that read the
  // executable PT_INTERP.
  insert_pt_interp_into_phdr_table(&args, &exe, loader.path);
  ri_close(loader.fd);

  // TODO: /proc/pid/auxv isn't updated with the new auxv vector. Is it possible to update it?
  // XXX: If we try to update it, we'd use prctl(PR_SET_MM, PR_SET_MM_AUXV, &vec, size, 0)
  // Maybe updating it would be useful as a way to communicate the loader's base to a debugger.
  // e.g. lldb uses AT_BASE in the aux vector, but it caches the values at process startup, so
  // it wouldn't currently notice a changed value.

  // The loader uses AT_BASE to locate itself, so search for the entry and update it. Even though
  // its value is always zero, the kernel still includes the entry[0]. If this changes (or we want
  // to make weaker assumptions about the kernel's behavior), then we can copy the kernel arguments
  // onto the stack (e.g. using alloca) before jumping to the loader's entry point.
  // [0] https://github.com/torvalds/linux/blob/v5.13/fs/binfmt_elf.c#L263
  for (size_t i = 0; i < args.auxv_count; ++i) {
    if (args.auxv[i].key == AT_BASE) {
      args.auxv[i].value = (unsigned long)interp.base_addr;
      debug("new auxv:");
      dump_auxv(&args);
      debug("transferring to real loader");
      return interp.entry;
    }
  }
  fatal("AT_BASE not found in aux vector");
}

asm(
"  .section " NOTE_SECTION_NAME ",\"a\",%note\n"
"  .balign 4\n"
"  .type relinterp, %object\n"
"relinterp:\n"
"  .long (2f-1f)\n"             // int32_t namesz
"  .long 256\n"                 // int32_t descsz
"  .long 5\n"                   // int32_t type (NT_TYPE_RELINTERP)
"1:.ascii \"Google\\0\"\n" // char name[]
"2:.balign 4\n"
"3:.ascii \"" LOADER_PATH "\\0\"\n"
"  .balign 4\n"
"4:.space 256-(4b-3b)\n"
"  .size relinterp, .-relinterp\n"
"  .text\n"
);
