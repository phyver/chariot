OCAMLBUILD=ocamlbuild -libs str,unix
# all: noninteractive-tests

all: native

tags:
	ctags *.ml

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

clean:
	ocamlbuild -clean
	rm -f main.native main.byte
	rm -f chariot
	rm -f tags
	rm -f gmon.out a.out

FORCE:
