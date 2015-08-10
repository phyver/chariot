INTERACTIVE="-i"

FILES=$(sort $(wildcard *.ch))
EXCLUDE=bug1.ch bug2.ch

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
