#pragma once

// Bionic(bionic/libc/kernel/tools/defaults.py) replaces udphdr
// with __kernel_udphdr and because of that including linux/udp.h
// is insufficient. Undo the renaming performed by the script.
#define __kernel_udphdr udphdr

#include_next <linux/udp.h>
