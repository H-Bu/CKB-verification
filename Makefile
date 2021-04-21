default: all

all: Blocks.v Stage_1.v Stage_2.v Stage_3.v Attack_simulation.v
	coqc Blocks.v
	coqc Stage_1.v
	coqc Stage_2.v
	coqc Stage_3.v
	coqc Attack_simulation.v

clean:
	rm *.vo*
	rm *.glob
	rm .*aux
	rm .lia.cache