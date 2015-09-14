OCAMLBUILD=ocamlbuild -libs str,unix


all: preproc native

tags:
	ctags *.ml

preproc: FORCE
	GIT_CURRENT_COMMIT=$(shell git rev-parse HEAD)
	@sed "s/let git_commit = \"GIT_CURRENT_COMMIT\"/let git_commit=\"$(GIT_CURRENT_COMMIT)\"/" version > version.ml
	@echo "let help_text = [" > help.ml
	@sed -e "s/\"/'/g" -e "s/^\(.*\)$$/  \"\1\";/" README >> help.ml
	@echo "  ]" >> help.ml

debug:
	$(OCAMLBUILD) -tag profile -tag debug main.native

native:
	$(OCAMLBUILD) main.native
	@ln -sf ./main.native ./chariot

byte:
	$(OCAMLBUILD) main.byte
	@ln -sf ./main.byte ./chariot

release:
	$(OCAMLBUILD) main.native -cflag "-noassert"
	@ln -sf ./main.native ./chariot

tests: native
	@echo "tests:"
	@make -s -C tests all

noninteractive-tests: native
	@make -s -C tests all INTERACTIVE="-n"
	@echo "ALL TESTS OK"

archive: release
	git archive --prefix=chariot/ -o chariot.tar HEAD

clean:
	ocamlbuild -clean
	rm -f main.native main.byte
	rm -f chariot
	rm -f tags
	rm -f gmon.out a.out

FORCE:
