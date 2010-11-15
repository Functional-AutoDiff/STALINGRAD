#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.67])
AC_INIT([Stalingrad],[0.0],[barak@cs.nuim.ie])
AC_CANONICAL_TARGET
AC_CONFIG_SRCDIR([QobiScheme/source/jdhuff.h])

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC
AC_PROG_RANLIB
AC_CHECK_PROG([AR], [ar], [ar])
AC_CHECK_PROG([SCC], [scc], [scc], [reject])
AC_CHECK_PROG([SCH], [sch], [sch], [reject])

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lX11':
AC_CHECK_LIB([X11], [XHostAddress])

AC_ARG_WITH([scxl], [AS_HELP_STRING([--with-scxl], [use Scheme->C X11 libraries])], [], [with_scxl=/usr/lib/scheme2c])

SCXL=
AS_IF([test "x$with_scxl" != xno],
        [AC_SUBST([SCXL], [$with_scxl])])


# Checks for header files.
AC_PATH_X
AC_CHECK_HEADERS([fcntl.h limits.h malloc.h memory.h netinet/in.h stddef.h stdlib.h string.h strings.h sys/param.h sys/time.h unistd.h])

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

AC_CONFIG_FILES([QobiScheme/Makefile
                 source/Makefile
                 Makefile])
AC_OUTPUT
