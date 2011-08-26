bin_PROGRAMS = cliche
man_MANS = cliche.1

EXTRA_DIST=$(man_MANS)

cliche_SOURCES = cliche.rl COPYING.cc
CLEANFILES=cliche.cc

COPYING.cc: ${top_srcdir}/COPYING
	(echo 'const char *COPYING=' \
	 && $(SED) -e 's/"/\\"/g' -e 's/^/\"/' -e 's/$$/\\n\"/' \
	 && echo ';') <$< >$@ || (rm $@;exit 1)

.rl.cc:
	$(RAGEL) -C -o $@ $<
