OCAMLBUILD=ocamlbuild -libs str,unix
# all: noninteractive-tests

GIT_CURRENT_COMMIT=$(shell git rev-parse HEAD)

all: native

tags:
	ctags *.ml

add_commit: FORCE
	@sed "s/let git_commit = \"GIT_CURRENT_COMMIT\"/let git_commit=\"$(GIT_CURRENT_COMMIT)\"/" version > version.ml

debug: add_commit
	$(OCAMLBUILD) -tag profile -tag debug main.native

native: add_commit
	$(OCAMLBUILD) main.native
	@ln -sf ./main.native ./chariot

byte: add_commit
	$(OCAMLBUILD) main.byte
	@ln -sf ./main.byte ./chariot

release: add_commit
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
	rm version.ml

FORCE:
