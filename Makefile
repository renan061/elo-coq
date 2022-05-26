# Makefile

COQC= coqc -Q . Elo

main:
	$(COQC) Array.v
	$(COQC) Mem.v
	$(COQC) Map.v
	$(COQC) Core0.v

clean:
	rm -f *.vo *.vok *.vos *.glob
