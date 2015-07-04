
FILES=$(sort $(wildcard *.ch))
EXCLUDE=

TESTS=$(filter-out $(EXCLUDE), $(FILES))

.SUFFIXES: .ch

all: $(TESTS)

%.ch: FORCE
	@./check.sh $@

FORCE:

very_clean: FORCE
	rm -f *.out
