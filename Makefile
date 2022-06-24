# Makefile

COQC= coqc -Q . Elo

main:
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core0.v
	$(COQC) Access.v
	$(COQC) Disjoint.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
