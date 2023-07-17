# Makefile

COQC= coqc -Q . Elo

all: soundness safety 

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Core.v
	$(COQC) CoreExt.v

meta: core
	$(COQC) AnyTerm.v
	$(COQC) Meta.v

memory: meta
	$(COQC) ValidAddresses.v
	$(COQC) References.v

soundness: memory
	$(COQC) Soundness.v

safety: soundness 
	$(COQC) Contains.v
	$(COQC) Access.v
	$(COQC) UnsafeAccess.v
	$(COQC) SafeSpawns.v
	$(COQC) SMS.v
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob
