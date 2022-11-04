# Makefile

COQC= coqc -Q . Elo

all: soundness safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v

access: core
	$(COQC) Access.v
	$(COQC) ValidAccesses.v

soundness: access 
	$(COQC) References.v
	$(COQC) Soundness.v

safety: soundness 
	$(COQC) Compat.v
	$(COQC) AccessProp.v
	$(COQC) Safe.v
	$(COQC) SMS.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
