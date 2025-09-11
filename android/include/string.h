#pragma once

#include_next <string.h>

/** C23 addition, copied from bionic for portability. */
static __inline void* memset_explicit(void* __dst, int __ch, size_t __n) {
  void* result = memset(__dst, __ch, __n);
  // https://bugs.llvm.org/show_bug.cgi?id=15495
  __asm__ __volatile__("" : : "r"(__dst) : "memory");
  return result;
}
