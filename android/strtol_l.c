/*
 * Copyright (C) 2026 The Android Open Source Project
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

#include <locale.h>
#include <stdlib.h>

// Upstream musl doesn't provide the strto*_l functions, but they are widely
// used.  Musl doesn't support locales, so add wrappers that ignore the locale
// and call the corresponding strto* functions.  Use wrappers instead of
// a bionic-style RENAME so that the original glibc-compatible symbols exist.
// Musl's weak_alias would be ideal, but that has to be in the same compilation
// unit which would require modifying the upstream strtol.c.

unsigned long long strtoull_l(const char *restrict s, char **restrict p, int base, locale_t locale) {
  return strtoll(s, p, base);
}

long long strtoll_l(const char *restrict s, char **restrict p, int base, locale_t locale) {
  return strtoll(s, p, base);
}

unsigned long strtoul_l(const char *restrict s, char **restrict p, int base, locale_t locale) {
  return strtoul(s, p, base);
}

long strtol_l(const char *restrict s, char **restrict p, int base, locale_t locale) {
  return strtol(s, p, base);
}
