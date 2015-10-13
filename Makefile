OCAMLBUILD=ocamlbuild -libs str,unix -I doc


all: native

tags:
	ctags *.ml

preproc: FORCE
	@echo "let git_commit=\"$(shell git rev-parse HEAD)\"" > version.ml
	@make -C doc

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
	tar --append --file=chariot.tar doc/*.ml --transform 's,doc/,chariot/doc/,'

install-vim:
	@install -d  ~/.vim/ftdetect/
	ln -sf $(PWD)/vim/ftdetect/chariot.vim  ~/.vim/ftdetect/
	@install -d ~/.vim/ftplugin/
	ln -sf $(PWD)/vim/ftplugin/chariot.vim  ~/.vim/ftplugin/
	@install -d ~/.vim/syntax/
	ln -sf $(PWD)/vim/syntax/chariot.vim  ~/.vim/syntax/

clean:
	ocamlbuild -clean
	rm -rf _build
	rm -f main.native main.byte
	rm -f chariot
	rm -f tags
	rm -f gmon.out a.out

FORCE:
