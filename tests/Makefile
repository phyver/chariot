INTERACTIVE="-i"

FILES=$(sort $(wildcard *.ch))
EXCLUDE=christophe.ch

TESTS=$(filter-out $(EXCLUDE), $(FILES))

.SUFFIXES: .ch

all: $(TESTS)

%.ch: FORCE
	@./check.sh -x "^=*\s*debug:" $(INTERACTIVE) $@

FORCE:

clean: FORCE
	rm -f *.tmpout

very_clean: FORCE
	rm -f *.tmpout *.out
