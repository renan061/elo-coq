# Makefile

COQC= coqc -Q . Elo

all: core syntactic-properties type-properties safety

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
	$(COQC) NoRef.v
	$(COQC) NoInit.v
	$(COQC) NoCR.v
	$(COQC) HasVar.v
	$(COQC) NoWRef.v
	$(COQC) ValidTerm.v
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
	$(COQC) ConsistentTerm.v
	$(COQC) PointerTypes.v
	$(COQC) Soundness.v
	$(COQC) SafeTerm.v
	$(COQC) ExclusivityInitCR.v
	$(COQC) TypeProperties.v

safety:
	# safety
	$(COQC) ConsistentRegions.v
	$(COQC) Multistep.v





access:
	# access 
	$(COQC) Access.v
	$(COQC) XAccess.v
	# WIP
	$(COQC) AccessInheritance.v
	$(COQC) AccessExclusivity.v
	$(COQC) NotAccess.v
	$(COQC) AccExc.v

todo1:
	$(COQC) HasRef.v
	$(COQC) PointerTypes.v
	$(COQC) NotXAccess.v
	$(COQC) Guards.v
	$(COQC) ClusteredAddresses.v

todo2:
	$(COQC) Promise.v
	$(COQC) Boundaries.v

oldsafety:
	$(COQC) SMS.v
	# $(COQC) Invariants.v
	# $(COQC) Safety.

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

