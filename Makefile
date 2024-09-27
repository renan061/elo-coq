# Makefile

COQC= coqc -Q . Elo

all: core properties preservation

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Core.v

properties:
	$(COQC) Definitions.v
	$(COQC) Inversions.v
	# $(COQC) Constructors.v
	$(COQC) Properties.v

preservation:
	$(COQC) SimpleLemmas.v
	$(COQC) Preservation.v


clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

