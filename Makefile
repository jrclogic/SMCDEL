COMPILER = ghc
GHCFLAGS = -Wall -pgml g++
HOMEDIR = $(shell (cd && pwd))

default:
	$(COMPILER) $(GHCFLAGS) DEMO_S5.hs HELP.hs KRIPKEVIS.hs
	$(COMPILER) $(GHCFLAGS) DELLANG.hs KRIPKEDEL.hs KNSCAC.hs SYMDEL.hs TEST.hs EXAMPLES.hs

otherbdds:
	$(COMPILER) $(GHCFLAGS) KNSCUDD.hs MyCUDD.hs KNSROB.hs KNSNOO.hs

BENCHMC:
	$(COMPILER) $(GHCFLAGS) MCTRIANGLE.hs BENCHMC.hs

BENCHDC:
	$(COMPILER) $(GHCFLAGS) BENCHDC.hs

experiments:
	$(COMPILER) $(GHCFLAGS) SAP.hs BDDREL.hs

all:
	make default
	make otherbdds
	make BENCHMC
	make BENCHDC
	make experiments

clean:
	rm -f *.o *.hi
	rm -f BENCHMC
	rm -f BENCHDC
