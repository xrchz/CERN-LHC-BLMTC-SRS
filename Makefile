HOLDIR := ~/HOL
HOLMAKE := $(HOLDIR)/bin/Holmake
.DEFAULT: proof.pdf
proof.pdf: proof.tex
	pdflatex $<
proof.tex: munge.exe overrides proof.pre.tex
	./$< overrides < proof.pre.tex > $@
munge.exe: ppTheory.uo
	$(HOLDIR)/src/TeX/mkmunge.exe $(basename $<)
ppTheory.uo: ppScript.sml ppTools.sml ppTools.sig simplifiedScript.sml annotation.sml annotation.sig
	$(HOLMAKE) $@
.PHONY: clean
clean:
	$(HOLMAKE) cleanAll
	rm -f proof.tex
