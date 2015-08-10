# all: noninteractive-tests

all: native

tags:
	ctags *.ml

debug:
	ocamlbuild -libs str,unix -tag profile -tag debug main.native

native:
	ocamlbuild -libs str,unix main.native
	@ln -sf ./main.native ./chariot

byte:
	ocamlbuild -libs str,unix main.byte
	@ln -sf ./main.byte ./chariot

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
