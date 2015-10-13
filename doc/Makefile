DOC_FILES=docSyntax.txt docTypes.txt docDef.txt docCommands.txt
DOC_FILES_ML=$(DOC_FILES:.txt=.ml)

all: FORCE $(DOC_FILES_ML)

%.ml: %.txt
	@echo "let help_text = [" > $@
	@sed -e "s/\"/'/g" -e "s/^\(.*\)$$/  \"\1\";/" title >> $@
	@sed -e "s/\"/'/g" -e "s/^\(.*\)$$/  \"\1\";/" $< >> $@
	@echo "  ]" >> $@

clean:
	rm -f *.ml

FORCE:
