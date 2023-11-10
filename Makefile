# Makefile

COQC= coqc -Q . Elo

all: core meta properties preservation soundness safety

core:
	$(COQC) Util.v
	$(COQC) Array.v
	$(COQC) Map.v
	$(COQC) Sem.v
	$(COQC) Ext.v
	$(COQC) Core.v

meta:
	$(COQC) Meta.v

properties:
	$(COQC) Definitions.v
	$(COQC) Inversions.v
	$(COQC) Constructors.v
	$(COQC) Properties.v

preservation:
	$(COQC) PtrTyp.v
	$(COQC) Lemmas.v
	$(COQC) Inheritance.v
	$(COQC) Preservation.v

# $(COQC) PropertiesVAD.v
# $(COQC) PropertiesACC.v
# $(COQC) PropertiesUACC.v
# $(COQC) PropertiesSS.v

soundness:
	$(COQC) Soundness.v

safety:
	$(COQC) Multistep.v
	$(COQC) Safety.v

clean:
	rm -f .lia.cache .*.aux *.vo *.vok *.vos *.glob

