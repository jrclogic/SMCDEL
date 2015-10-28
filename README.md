# SMCDEL

A symbolic model checker for Dynamic Epistemic Logic.

Complete literate Haskell documentation is in SMCDEL.pdf.

See also: Johan van Benthem, Jan van Eijck, Malvin Gattinger, and Kaile Su: Symbolic Model Checking for Dynamic Epistemic Logic. In: Proceedings of The Fifth International Conference on Logic, Rationality and Interaction (LORI-V), 2015.


## Basic usage

0) Install dependencies:

- use the latest Haskell Platform from https://www.haskell.org/platform/
- cabal update
- cabal install alex happy ansi-terminal
- get HasCacBDD from https://github.com/m4lvin/HasCacBDD

1) Build the standalone executable by running "make".

2) Create a text file which describes the knowledge structure and the formulas you want to check for truth or validity:

    -- examples/MuddyShort.smcdel
    -- Three Muddy Children in SMCDEL
    VARS
      1,2,3
    LAW
      Top
    OBS
      alice: 2,3
      bob: 1,3
      carol: 1,2
    VALID?
      (not (alice knows whether 1) & not (bob knows whether 2) & not (carol knows whether 3))

3) Run "SMCDEL textfile.smcdel" resulting in:

    >> ./SMCDEL examples/MuddyShort.smcdel
    SMCDEL 1.0 by -- https://github.com/jrclogic/SMCDEL

    Is Conj [Conj [Neg (Kw "alice" (PrpF (P 1))),Neg (Kw "bob" (PrpF (P 2)))],Neg (Kw "carol" (PrpF (P 3)))] valid on the given structure?
    True

    Doei!

More .smcdel files are in the "examples" folder.


## Advanced usage

To deal with more complex models and formulas, use SMCDEL as a Haskell module.

Examples can be found in EXAMPLES.hs and the BENCH*.hs modules.


## Used BDD packages

SMCDEL can be used with four different BDD packages. To compile and
run the benchmark BENCHMC you will have to install all of them.

* Data.HasCacBDD from https://github.com/m4lvin/HasCacBDD which runs CacBDD from http://kailesu.net/CacBDD/

* Data.Boolean.CUDD from https://github.com/peteg/hBDD (with some patches, see https://github.com/m4lvin/hBDD)

* Data.ROBDD from https://github.com/travitch/robbed

* Data.NooBDD from https://github.com/m4lvin/NooBDD


## Source Code Overview

File         | Content                               | chapter in SMCDEL.pdf
------------ | ------------------------------------- | ---------------------
BDDREL.hs    | experimental module for non-S5 models | Appendix 4
BENCHDC.hs   | Dining Cryptographers benchmark       | 7.1
BENCHMC.hs   | Muddy Children benchmark              | 7.2
BENCHSAP.hs  | Sum and Product benchmark             |
DELLANG.hs   | definition of the DEL Language        | 1
DEMO_S5.hs   | modified version of DEMO-S5           |
EXAMPLES.hs  | many examples                         | 6
HELP.hs      | helper module                         | Appendix 2
KNSCAC.hs    | definitions of KNS and translations   | 3
KNSCUDD.hs   | KNSCAC variant for Data.Boolean.CUDD  |
KNSNOO.hs    | KNSCAC variant for Data.NooBDD        |
KNSROB.hs    | KNSCAC variant for Data.ROBDD         |
KRIPKEDEL.hs | simple explicit model checking        | 2
KRIPKEVIS.hs | visualisation for Kripke models       |
Lex.x        | alex file to generate a lexer         | 8.2
LICENSE      | GNU General Public License v2         |
Makefile     | build instructions for GNU make       |
MCTRIANGLE.hs| Muddy children via number triangle    | Appendix 3
MyCUDD.hs    | a wrapper for Data.Boolean.CUDD       |
Parse.y      | happy file to generate a parser       | 8.2
README.md    | this file                             |
SAPTRANS.hs  | Sum and Product via translation       |
SMCDEL.hs    | standalone executable                 | 8.1
SMCDEL.pdf   | documentation in literate Haskell     |
SYMDEL.hs    | back and forth between Kripke and KNS | 4
TEST.hs      | automated tests                       | 5
Token.hs     | list of tokens for alex and happy     | 8.2
examples     | folder with example .smcdel files     |
