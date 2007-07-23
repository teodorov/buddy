EXTRA_DIST = \
    bddnotes.ps \
    buddy.ps \
    tech.txt 

dist-hook: html
	cp -a $(srcdir)/html $(distdir)/html

html-local:
	-rm -rf html
	doxygen conf.doxyfile

maintainer-clean-local:
	@echo 'This command is intended for maintainers to use; it'
	@echo 'deletes files that may need special tools to rebuild.'
	-rm -r html


