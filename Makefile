COMPILER = ghc
GHCFLAGS = -Wall -pgml g++

SMCDEL: *.hs
	make Lex.o
	make Parse.o
	$(COMPILER) $(GHCFLAGS) SMCDEL.hs

Lex.o: Lex.x
	alex Lex.x
	ghc -fno-warn-tabs Lex.hs

Parse.o: Parse.y
	happy Parse.y
	ghc Parse.hs

otherbdds:
	$(COMPILER) $(GHCFLAGS) KNSCUDD.hs MyCUDD.hs KNSROB.hs KNSNOO.hs

BENCHMC:
	$(COMPILER) $(GHCFLAGS) MCTRIANGLE.hs BENCHMC.hs

BENCHDC:
	$(COMPILER) $(GHCFLAGS) BENCHDC.hs

BENCHSAP:
	$(COMPILER) $(GHCFLAGS) BENCHSAP.hs

experiments:
	$(COMPILER) $(GHCFLAGS) BDDREL.hs SAPTRANS.hs

all:
	make SMCDEL
	make otherbdds
	make BENCHMC
	make BENCHDC
	make BENCHSAP
	make experiments

clean:
	rm -f *.o *.hi
	rm -f Lex.hs Parse.hs
	rm -f BENCHMC
	rm -f BENCHDC
	rm -f BENCHSAP
	rm -f SAPTRANS
	rm -f SMCDEL
