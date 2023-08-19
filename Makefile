# Makefile

COQC= coqc -Q . Elo

all: core meta definitions properties soundness safety

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v
	$(COQC) CoreExt.v

meta:
	$(COQC) AnyTerm.v
	$(COQC) Meta.v

definitions:
	$(COQC) ValidAddresses.v
	$(COQC) WellTypedTerm.v
	$(COQC) CTR.v
	$(COQC) Access.v
	$(COQC) UnsafeAccess.v
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v
	$(COQC) Definitions.v
	$(COQC) Sanity.v

properties:
	$(COQC) MemTyp.v
	$(COQC) PropertiesVAD.v
	$(COQC) PropertiesCTR.v
	$(COQC) PropertiesACC.v
	$(COQC) PropertiesUACC.v
	$(COQC) PropertiesSS.v
	$(COQC) PropertiesSMS.v

soundness:
	$(COQC) Soundness.v

safety:
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

