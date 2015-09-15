OCAMLBUILD=ocamlbuild -libs str,unix


all: native

tags:
	ctags *.ml

preproc: FORCE
	@echo "let git_commit=\"$(shell git rev-parse HEAD)\"" > version.ml
	@echo "let help_text = [" > help.ml
	@sed -e "s/\"/'/g" -e "s/^\(.*\)$$/  \"\1\";/" README >> help.ml
	@echo "  ]" >> help.ml

debug:
	$(OCAMLBUILD) -tag profile -tag debug main.native
	@ln -sf ./main.native ./chariot

native:
	$(OCAMLBUILD) main.native
	@ln -sf ./main.native ./chariot

byte:
	$(OCAMLBUILD) main.byte
	@ln -sf ./main.byte ./chariot

release:
	$(OCAMLBUILD) main.native -cflag "-noassert"
	@cp ./main.native ./chariot

tests: native
	@echo "tests:"
	@make -s -C tests all

noninteractive-tests: native
	@make -s -C tests all INTERACTIVE="-n"
	@echo "ALL TESTS OK"

archive: preproc
	git archive --prefix=chariot/ -o chariot.tar HEAD
	tar --append --file=chariot.tar version.ml --transform 's,version.ml,chariot/version.ml,'

clean:
	ocamlbuild -clean
	rm -rf _build
	rm -f main.native main.byte
	rm -f chariot
	rm -f tags
	rm -f gmon.out a.out

FORCE:
