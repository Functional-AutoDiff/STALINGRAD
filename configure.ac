#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.67])
AC_INIT([Stalingrad], [0.0], [barak@cs.nuim.ie])

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_LN_S

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_FORK
AC_FUNC_MALLOC
AC_FUNC_MMAP
AC_FUNC_REALLOC
AC_FUNC_STRTOD
AC_CHECK_FUNCS([bzero dup2 floor ftime getcwd gettimeofday memset pow select socket sqrt strerror strrchr])

AC_CONFIG_FILES([QobiScheme-1.44/source/Makefile
                 infrastructure-1.27/Makefile
                 map-closure/source/Makefile
                 source/Makefile])
AC_OUTPUT
