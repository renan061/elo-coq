# Makefile

COQC= coqc -Q . Elo

all: core meta memory soundness access safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v
	$(COQC) CoreExt.v

meta:
	$(COQC) AnyTerm.v
	$(COQC) Meta.v

memory:
	$(COQC) ValidAddresses.v
	$(COQC) References.v

soundness:
	$(COQC) Soundness.v

access:
	$(COQC) AccessCore.v
	$(COQC) NotAccess.v
	$(COQC) AccessExtra.v
	$(COQC) UnsafeAccess.v
	$(COQC) Access.v

safety:
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
