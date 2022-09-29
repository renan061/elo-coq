# Makefile

COQC= coqc -Q . Elo

main: core
	$(COQC) Compat.v
	$(COQC) AccessProp.v
	$(COQC) NoLoc.v
	$(COQC) Disjoint.v

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v

soundness: core
	$(COQC) Access.v
	$(COQC) References.v
	$(COQC) Soundness.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
