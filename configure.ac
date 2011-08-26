AC_INIT([cliche],[0.0],[cliche-bugs@klever.net])
AC_CONFIG_SRCDIR([src/cliche.rl])
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE([check-news dist-bzip2 parallel-tests color-tests])

AC_PROG_INSTALL
AC_PROG_CXX
AC_PATH_PROG([RAGEL],[ragel],[false])
test "$RAGEL" = "false" && AC_MSG_ERROR([No ragel FSM compiler found])
AC_PROG_SED

AC_PATH_PROG([XSLTPROC],[xsltproc],[true])

AC_CHECK_FUNC([getopt_long],[
 AC_DEFINE([HAVE_GETOPT_LONG],[1],[define to make use of getopt_long])
])

AC_CONFIG_FILES([
 Makefile
 src/Makefile
 test/Makefile
])
AC_OUTPUT
