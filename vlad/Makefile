all: manual.pdf manual.info manual.html

%.html: %.texi; $(MAKEINFO) --html --no-split $^
%.pdf: %.texi; texi2pdf $^

.PHONY: all
