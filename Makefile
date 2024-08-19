.PHONY: build clean docs

-include Makefile.coq

COQCFLAGS := -noinit -indices-matter 
COQCFLAGS := $(foreach FLAG, $(COQCFLAGS), -arg $(FLAG))

COQMFFLAGS := -Q . TypesAndCats
COQDOCFLAGS := --utf8

ALLVFILES := Primitives.v Types.v Paths.v

build:
	$(MAKE) -f Makefile.coq

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) *.html

docs:
	coqdoc $(COQDOCFLAGS) $(ALLVFILES)

Makefile.coq:
	coq_makefile $(COQMFFLAGS) $(COQCFLAGS) -o Makefile.coq $(ALLVFILES)