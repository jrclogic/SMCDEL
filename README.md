# SMCDEL

A symbolic model checker for Dynamic Epistemic Logic.

Complete literate Haskell documentation is in [SMCDEL.pdf](SMCDEL.pdf).

See also: [Johan van Benthem, Jan van Eijck, Malvin Gattinger, and Kaile Su: Symbolic Model Checking for Dynamic Epistemic Logic. In: Proceedings of The Fifth International Conference on Logic, Rationality and Interaction (LORI-V), 2015](http://dx.doi.org/10.1007/978-3-662-48561-3_30).


## Online

You can try SMCDEL online here: https://w4eg.de/malvin/illc/smcdelweb


## Basic usage

1) Use *stack* from https://www.stackage.org

- `stack build` will compile everything. This might fail if one of
  the BDD packages written in C and C++ is missing. See `Makefile`
  for extra library paths and try `make` instead.
- `stack install` will put two executables `smcdel` and `smcdel-web`
  into ~/.local/bin which should be in your PATH variable.

2) Create a text file which describes the knowledge structure and
the formulas you want to check for truth or validity:

    -- Three Muddy Children in SMCDEL
    VARS 1,2,3
    LAW  Top
    OBS  alice: 2,3
         bob:   1,3
         carol: 1,2
    WHERE?
      [ ! (1|2|3) ] alices knows whether 1
    VALID?
      [ ! (1|2|3) ]
      [ ! ((~ (alice knows whether 1)) & (~ (bob knows whether 2)) & (~ (carol knows whether 3))) ]
      [ ! ((~ (alice knows whether 1)) & (~ (bob knows whether 2)) & (~ (carol knows whether 3))) ]
      (alice,bob,carol) comknow that (1 & 2 & 3)

3) Run "smcdel textfile" resulting in:

    >> smcdel MuddyShort.smcdel.txt
    SMCDEL 1.0 by Malvin Gattinger -- https://github.com/jrclogic/SMCDEL

    At which states is ... true?
    []
    [1]

    Is ... valid on the given structure?
    True

More example files are in `Examples/`.


## Advanced usage

To deal with more complex models and formulas, use SMCDEL as a Haskell module.

Examples can be found in `Examples.hs` and the `Bench` folder.


## Used BDD packages

SMCDEL can be used with four different BDD packages. To compile and
run the benchmarks you will have to install all of them.

- [Data.HasCacBDD](https://github.com/m4lvin/HasCacBDD) from  which runs CacBDD from http://kailesu.net/CacBDD/
- [Data.Boolean.CUDD](https://github.com/peteg/hBDD) ([with some patches](https://github.com/m4lvin/hBDD))
- [Data.ROBDD](https://github.com/travitch/robbed)
- [Data.NooBDD](https://github.com/m4lvin/NooBDD)

## Experimental Stuff

- `SMCDEL.Symbolic.SatZ3` uses the SAT solver Z3 for symbolic evaluation.
- `SMCDEL.Other.NonS5` implements general knowledge structures. They are
  equivalent to Kripke models which are not based on equivalence relations.
