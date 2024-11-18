# Makefile

COQC= coqc -Q . Elo

all: core properties1 properties2

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Upsilon.v
	$(COQC) Values.v
	$(COQC) Core.v

properties1:
	$(COQC) WellTypedTerm.v
	$(COQC) ValidAddresses.v
	$(COQC) NoInit.v
	$(COQC) NoCR.v
	$(COQC) ValidBlocks.v
	$(COQC) Inheritance1.v
	$(COQC) OneInit.v
	$(COQC) OneCR.v
	$(COQC) Properties1.v

properties2:
	$(COQC) NoUninitRefs.v
	$(COQC) UniqueInits.v
	$(COQC) UniqueCRs.v
	$(COQC) ConsistentInits.v
	$(COQC) ConsistentRefs.v
	$(COQC) Soundness.v

properties3:
	$(COQC) XArea.v

access:
	$(COQC) NoRef.v
	$(COQC) AccessCore.v
	$(COQC) PointerTypes.v
	$(COQC) NotAccess.v
	$(COQC) Boundaries1.v
	$(COQC) Inheritance.v
	$(COQC) Promise.v

todo:
	$(COQC) Boundaries.v

safety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

