# SMCDEL

A symbolic model checker for Dynamic Epistemic Logic.

Complete literate Haskell documentation is in SMCDEL.pdf.

See also: Johan van Benthem, Jan van Eijck, Malvin Gattinger, and Kaile Su: Symbolic model checking for dynamic epistemic logic. In: Proceedings of The Fifth International Conference on Logic, Rationality and Interaction (LORI-V), 2015.


## Basic usage

0) Install HasCacBDD from https://github.com/m4lvin/HasCacBDD

1) Build the standalone executable by running "make".

2) Create a text file which describes the model and the formulas you want to check for truth or validity:

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

SMCDEL can be used with four different BDD packages.

* Data.HasCacBDD from https://github.com/m4lvin/HasCacBDD which runs CacBDD from http://kailesu.net/CacBDD/

* Data.Boolean.CUDD from https://github.com/peteg/hBDD (with some patches, see https://github.com/m4lvin/hBDD)

* Data.ROBDD from https://github.com/travitch/robbed

* Data.NooBDD from https://github.com/m4lvin/NooBDD
