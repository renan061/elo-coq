# Makefile

COQC= coqc -Q . Elo

all: soundness safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v
	$(COQC) Access.v

soundness: core
	$(COQC) References.v
	$(COQC) Soundness.v

safety: core
	$(COQC) Compat.v
	$(COQC) AccessProp.v
	$(COQC) NoLoc.v
	$(COQC) Disjoint.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
