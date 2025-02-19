main=rsmg5
collectionID=FX2URPTD

default:
	latexmk ${main}.tex -pdf -synctex=1

zotero:
	curl 'http://127.0.0.1:23119/better-bibtex/export/collection?/1/${collectionID}.biblatex' \
	  --output references.bib

clean:
	rm -f *.aux\
	      *.dvi\
	      *.toc\
	      *.ps\
	      *.pdf\
	      *.log\
	      *.bbl\
	      *.blg\
	      *.lox\
	      *.fdb_latexmk\
	      *.fls\
	      *.out\
	      *.bcf\
	      *.vtc\
	      *.run.xml\
