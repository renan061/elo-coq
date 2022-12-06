# Makefile

COQC= coqc -Q . Elo

all: soundness safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v

access: core
	$(COQC) HasAddress.v
	$(COQC) ValidAddresses.v
	$(COQC) Access.v
	$(COQC) ValidAccesses.v
	$(COQC) Contains.v
	$(COQC) References.v

soundness: access 
	$(COQC) Soundness.v

safety: soundness 
	$(COQC) AccessProp.v
	$(COQC) UnsafeAccess.v
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
