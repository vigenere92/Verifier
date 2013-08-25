AC_PREREQ([2.68])
AC_INIT([Verifier], [1.0], [sgauarav@iitrpr.ac.in,shubhammodi21@gmail.com])
AC_CONFIG_SRCDIR([Includes/pugixml/contrib/foreach.hpp])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE(Verifier, 1.0)
AC_PROG_CXX
AC_LANG([C++])
echo "checking for lemon graph library package..."
AC_COMPILE_IFELSE([AC_LANG_PROGRAM([[#include <lemon/list_graph.h>]],[[ lemon::ListDigraph graph;]])],[have_lemon=[yes]],[have_lemon=[no]])
if test x"$have_lemon" = x"yes"; then
  AC_MSG_RESULT([yes])
else
  AC_MSG_RESULT([no])
fi
AC_CHECK_PROG([have_z3], [z3], [yes], [no])
AC_CHECK_PROG([have_pdflatex], [pdflatex], [yes], [no])
AC_CHECK_HEADERS([iostream])
AC_CHECK_HEADERS([float.h stddef.h stdint.h stdlib.h string.h sys/time.h wchar.h])
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT8_T
AC_CHECK_TYPES([ptrdiff_t])
AC_FUNC_ERROR_AT_LINE
AC_FUNC_MALLOC
AC_FUNC_STRTOD
AC_CHECK_FUNCS([floor memmove pow strchr strstr strtol strtoul])
if test $have_z3 = "no"; then
    echo "Z3 SMT solver not found. Please install the Z3 SMT solver for the Verifier to work"
fi
if test $have_pdflatex = "no"; then
    echo "pdflatex not found. Please install the pdflatex package for generating pdf files for the results of Verifier"
fi
if test $have_z3 = "yes";then
    if test $have_lemon = "yes";then
        AC_OUTPUT(Makefile src/Makefile)
        echo Configure complete, now type \'make\' and then \'sudo make install\'.
    fi
else
    echo "Configuration Failed"
fi
