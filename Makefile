# Makefile

COQC= coqc -Q . Elo

main:
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core0.v
	$(COQC) Access.v
	$(COQC) Compat.v
	$(COQC) WBA.v
	$(COQC) AccessProp.v
	$(COQC) NoLoc.v
	$(COQC) Disjoint.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
