
FILES=$(sort $(wildcard *.ch))
EXCLUDE=

TESTS=$(filter-out $(EXCLUDE), $(FILES))

.SUFFIXES: .ch

all: $(TESTS)

%.ch: FORCE
	@./check.sh $@

FORCE:

clean: FORCE
	rm -f *.tmpout

very_clean: FORCE
	rm -f *.tmpout *.out
