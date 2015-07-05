all: native

tags:
	ctags *.ml

debug:
	ocamlbuild -libs str,unix -tag profile -tag debug main.native

native:
	ocamlbuild -libs str,unix main.native

byte:
	ocamlbuild -libs str,unix main.byte

tests: FORCE
	make -C tests all

clean:
	ocamlbuild -clean
	rm -f tags
	rm -f main.native main.byte
	rm -f gmon.out a.out

FORCE:
