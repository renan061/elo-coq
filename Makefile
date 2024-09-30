# Makefile

COQC= coqc -Q . Elo

all: core properties

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Core.v

properties:
	$(COQC) Preservation_.v
	$(COQC) WellTypedTerm.v
	$(COQC) ValidPointerTypes.v
	$(COQC) ValidAddresses.v
	$(COQC) ValidReferences.v
	# $(COQC) CTR.v
	# $(COQC) Definitions.v
	# $(COQC) Inversions.v
	# $(COQC) Constructors.v
	# $(COQC) Properties.v

preservation:
	$(COQC) SimpleLemmas.v
	$(COQC) Preservation.v


clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

