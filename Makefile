# Makefile

COQC= coqc -Q . Elo

all: core properties access

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Upsilon.v
	$(COQC) Values.v
	$(COQC) Core.v

properties:
	$(COQC) Addresses.v
	$(COQC) Blocks.v
	$(COQC) WellTypedTerm.v
	$(COQC) NoRef.v
	$(COQC) Inits.v
	$(COQC) Refs.v
	$(COQC) Soundness.v
	$(COQC) CriticalRegions.v
	$(COQC) XArea.v
	#$(COQC) PointerTypes.v
	$(COQC) Properties.v

access:
	$(COQC) AccessCore.v
	$(COQC) NotAccess.v
	$(COQC) Boundaries1.v
	$(COQC) Inheritance.v

todo:
	$(COQC) Boundaries.v

safety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

