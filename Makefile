# Makefile

COQC= coqc -Q . Elo

main: core
	$(COQC) Access.v
	$(COQC) Compat.v
	$(COQC) WBA.v
	$(COQC) AccessProp.v
	$(COQC) NoLoc.v
	$(COQC) Disjoint.v

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v

soundness: core
	$(COQC) References.v
	$(COQC) Access.v
	$(COQC) WBA.v
	$(COQC) Soundness.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
