# Makefile

COQC= coqc -Q . Elo

all: core syntactic-properties type-properties

core:
	# core
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Upsilon.v
	$(COQC) Values.v
	$(COQC) Core.v

syntactic-properties:
	# syntactic properties
	$(COQC) ValidAddresses.v
	$(COQC) HasVar.v
	$(COQC) NoRef.v
	$(COQC) NoWRef.v
	$(COQC) NoInit.v
	$(COQC) NoCR.v
	$(COQC) ValidBlocks.v
	$(COQC) InheritanceNoInit.v
	$(COQC) InheritanceNoCR.v
	$(COQC) OneInit.v
	$(COQC) OneCR.v
	$(COQC) NoUninitRefs.v
	$(COQC) UniqueInits.v
	$(COQC) UniqueCRs.v
	$(COQC) SyntacticProperties.v

type-properties:
	# type properties
	$(COQC) WellTypedTerm.v
	$(COQC) ConsistentInits.v
	$(COQC) ConsistentRefs.v
	$(COQC) Soundness.v
	$(COQC) SafeNewX.v
	$(COQC) SafeAcq.v
	$(COQC) TypeProperties.v

properties2:
	$(COQC) ValidSpawns.v
	$(COQC) InitCR.v
	$(COQC) Properties2.v

ownership:
	$(COQC) AccessCore.v
	$(COQC) Ownership.v

access:
	$(COQC) AccessInheritance.v
	$(COQC) AccessExclusivity.v
	$(COQC) NotAccess.v
	$(COQC) AccExc.v

todo1:
	$(COQC) HasRef.v
	$(COQC) PointerTypes.v
	$(COQC) NotXAccess.v
	$(COQC) Guards.v

todo2:
	$(COQC) Promise.v
	$(COQC) Boundaries.v

safety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

