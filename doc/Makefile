.PHONY : clean realclean
.PRECIOUS : %.tex

default: Readme.pdf

%.pdf : latex/doc/%.tex agda.sty
	latexmk --pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

latex/doc/%.tex : %.lagda.tex
	agda --latex $<

clean:
	rm -f *.aux *.log *.out *.ptb *.blg *.fdb_latexmk *.agdai *.fls *.toc *~

realclean: clean
	rm -f *.glob *.vo *.bbl latex/doc/* agda.pdf


