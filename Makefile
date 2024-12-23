# Makefile

COQC= coqc -Q . Elo

all: core syntactic-properties type-properties safety examples

core:
	# core
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) SemExt.v
	$(COQC) Kappa.v
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
	$(COQC) Exclusivity.v
	$(COQC) ConsistentRegions.v
	$(COQC) TypeProperties.v

safety:
	# safety
	$(COQC) Multistep.v

examples:
	# examples
	$(COQC) Examples.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

