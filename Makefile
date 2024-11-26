# Makefile

COQC= coqc -Q . Elo

all: core properties1 properties2 access

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
	$(COQC) NoRef.v
	$(COQC) NoWRef.v
	$(COQC) NoUninitRefs.v
	$(COQC) UniqueInits.v
	$(COQC) UniqueCRs.v
	$(COQC) ConsistentInits.v
	$(COQC) ConsistentRefs.v
	$(COQC) Soundness.v
	$(COQC) InitCR.v
	$(COQC) Properties2.v

access:
	$(COQC) AccessCore.v
	$(COQC) AccessInheritance.v
	$(COQC) AccessExclusivity.v
	$(COQC) PointerTypes.v
	$(COQC) NotAccess.v
	$(COQC) NotXAccess.v
	$(COQC) Guards.v

todo:
	$(COQC) HasRef.v
	$(COQC) SafeNewX.v
	$(COQC) Promise.v
	$(COQC) Boundaries.v

safety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

