SUBDIRS=src test

all-local: NEWS

NEWS: NEWS.xsl NEWS.xml
	$(XSLTPROC) -o $@ $^
EXTRA_DIST = NEWS.xml NEWS.xsl

ISSUEFILES = $$(find ${top_srcdir} -type f '(' \
	-name '*.rl' -or -name '*.h' \
	')' ) \
	${top_srcdir}/configure.ac
issues: todo fixme xxx
todo fixme xxx:
	@grep --color=auto -in '$@:' ${ISSUEFILES} || true
