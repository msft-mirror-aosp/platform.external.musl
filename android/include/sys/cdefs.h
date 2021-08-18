#pragma once

/* Unlike glibc, musl does not #define __MUSL__ on the assumption that
 * building against musl will be done using a configure script that should
 * be testing for individual features rather than assuming them based on
 * using musl.  We don't use configure-based builds, so add a local
 * ANDROID_HOST_MUSL macro that will be defined for all host musl builds.
 */
#define ANDROID_HOST_MUSL 1

#if defined(__cplusplus)
#define __BEGIN_DECLS extern "C" {
#define __END_DECLS }
#else
#define __BEGIN_DECLS
#define __END_DECLS
#endif
