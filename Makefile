all: native

native:
	ocamlbuild -libs str,unix main.native

byte:
	ocamlbuild -libs str,unix main.byte

clean:
	ocamlbuild -clean
