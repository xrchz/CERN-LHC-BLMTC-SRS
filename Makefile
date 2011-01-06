HOLDIR := ~/HOL
HOLMAKE := $(HOLDIR)/bin/Holmake
.DEFAULT: proof.pdf
proof.pdf: proof.tex
	pdflatex $<
proof.tex: munge.exe overrides proof.pre.tex
	./$< overrides < proof.pre.tex > $@
munge.exe: simplifiedTheory.uo
	$(HOLDIR)/src/TeX/mkmunge.exe $(basename $<)
simplifiedTheory.uo: simplifiedScript.sml
	$(HOLMAKE) $@
.PHONY: clean
clean:
	$(HOLMAKE) cleanAll
	rm -f proof.tex
