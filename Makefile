all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

COQMODULES := $(patsubst src/BellantoniCook/%.v,BellantoniCook.%,$(wildcard src/BellantoniCook/*.v))

check: all
	$(COQBIN)coqchk -silent -R src/BellantoniCook BellantoniCook $(COQMODULES)

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq src/BellantoniCook/*.v

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all check clean _CoqProject Makefile
