#ifndef _SYS_PRCTL_H
#define _SYS_PRCTL_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

/*
 * Get the constants and structs from uapi so that code that
 * includes <linux/prctl.h> doesn't conflict with <sys/prctl.h>.
 */
#include <linux/prctl.h>

int prctl (int, ...);

#ifdef __cplusplus
}
#endif

#endif
