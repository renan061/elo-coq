# Makefile

COQC= coqc -Q . Elo

all: soundness safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v
	$(COQC) CoreExt.v

access: core
	$(COQC) HasAddress.v
	$(COQC) ValidAddresses.v
	$(COQC) Access.v
	$(COQC) Contains.v
	$(COQC) References.v

soundness: access 
	$(COQC) Soundness.v

safety: soundness 
	$(COQC) UnsafeAccess.v
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
