TESTS=\
	r01_closing_at_the_line_start.clichec \
	r02_anchor_after_literal.clichec \
	r03_percent_after_empty.clichec \
	r04_too_seamless_transitions.clichec

EXTRA_DIST=$(TESTS)
CLEANFILES = $(basename $(TESTS)) \
	$(foreach s,.out .diff,$(addsuffix $s,$(basename $(TESTS))))
.INTERMEDIATE: $(CLEANFILES)

TEST_EXTENSIONS=.clichec
CLICHEC_LOG_COMPILER=test_clichec() { \
 $(MAKE) "$$(basename $$1 .clichec)"{,.{out,diff,check}} ;\
}; test_clichec

gitignore: .gitignore
.gitignore: Makefile
	for t in ${TESTS} ; do for f in "$${t%.*}"{,.{out,diff,check,log}} ; do \
	 grep -q "^/$$f" .gitignore || echo "/$$f" >>.gitignore ;\
	done done

CLICHE=${top_builddir}/src/cliche
SUFFIXES=.clichec .cc .out .diff .check
.clichec.cc:
	$(CLICHE) -C -o $@ $<
%.out: %
	${builddir}/$< >$@
%.diff: ${builddir}/%.out ${srcdir}/%.expected
	@-diff -u "$*.expected" "$*.out" >"$@"
%.check: %.diff
	@test -s "$<" && { cat "$*.out";cp "$*.out" "$*.unexpected" ; exit 1 ; } || true
