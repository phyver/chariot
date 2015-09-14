OCAMLBUILD=ocamlbuild -libs str,unix
# all: noninteractive-tests

GIT_CURRENT_COMMIT=$(shell git rev-parse HEAD)

all: native

tags:
	ctags *.ml

add_commit: FORCE
	@sed "s/let git_commit = \"GIT_CURRENT_COMMIT\"/let git_commit=\"$(GIT_CURRENT_COMMIT)\"/" version > version.ml

help_file: FORCE
	@echo "let help_text = [" > help.ml
	@sed -e "s/\"/'/g" -e "s/^\(.*\)$$/  \"\1\";/" README >> help.ml
	@echo "  ]" >> help.ml

debug: add_commit help_file
	$(OCAMLBUILD) -tag profile -tag debug main.native

native: add_commit help_file
	$(OCAMLBUILD) main.native
	@ln -sf ./main.native ./chariot

byte: add_commit help_file
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

clean:
	ocamlbuild -clean
	rm -f main.native main.byte
	rm -f chariot
	rm -f tags
	rm -f gmon.out a.out

FORCE:
