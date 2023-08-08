# Makefile

COQC= coqc -Q . Elo

all: core meta definitions properties 

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
	$(COQC) NotAccess.v
	$(COQC) UnsafeAccess.v
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v
	$(COQC) Definitions.v

soundness:
	$(COQC) Soundness.v

properties:
	$(COQC) PropertiesVAD.v
	$(COQC) PropertiesCTR.v

todo:
	$(COQC) WttPreservation.v
	$(COQC) NaccPreservation.v
	$(COQC) NuaccPreservation.v

access:
	$(COQC) AccessExtra.v

safety:
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
