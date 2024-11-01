# Makefile

COQC= coqc -Q . Elo

all: core properties todo 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Core.v

properties:
	$(COQC) WellTypedTerm.v
	$(COQC) ValidReferences.v
	$(COQC) Soundness.v
	$(COQC) Properties.v

todo:
	$(COQC) CriticalRegions.v
	$(COQC) Boundaries.v
	$(COQC) Access.v

safety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

