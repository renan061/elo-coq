# Makefile

COQC= coqc -Q . Elo

main:
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core0.v
	$(COQC) Access.v

clean:
	rm -f *.vo *.vok *.vos *.glob
