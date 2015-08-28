INTERACTIVE="-i"

FILES=$(sort $(wildcard *.ch))
EXCLUDE=angel-sct.ch

TESTS=$(filter-out $(EXCLUDE), $(FILES))

.SUFFIXES: .ch

all: $(TESTS)

%.ch: FORCE
	@./check.sh -x "^--==" $(INTERACTIVE) $@

FORCE:

clean: FORCE
	rm -f *.tmpout

very_clean: FORCE
	rm -f *.tmpout *.out
