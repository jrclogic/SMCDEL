# SMCDEL

[![Release](https://img.shields.io/github/release/jrclogic/SMCDEL.svg)](https://github.com/jrclogic/SMCDEL/releases)
[![Hackage](https://img.shields.io/hackage/v/smcdel.svg)](https://hackage.haskell.org/package/smcdel)
[![GitLab CI](https://gitlab.com/m4lvin/SMCDEL/badges/master/pipeline.svg)](https://gitlab.com/m4lvin/SMCDEL/-/pipelines)
[![Test Coverage](https://gitlab.com/m4lvin/SMCDEL/badges/master/coverage.svg)](https://gitlab.com/m4lvin/SMCDEL/-/jobs/artifacts/master/file/hpc/combined/all/hpc_index.html?job=test)
[![DOI](https://zenodo.org/badge/36519077.svg)](https://zenodo.org/badge/latestdoi/36519077)

A symbolic model checker for [Dynamic Epistemic Logic](https://plato.stanford.edu/entries/dynamic-epistemic).


## Online

You can try SMCDEL online here: https://w4eg.de/malvin/illc/smcdelweb/


## Basic usage

1) Use *stack* from https://www.stackage.org

- `stack install` will build and install an executable `smcdel`
  into `~/.local/bin` which should be in your `PATH` variable.

2) Create a text file `MuddyShort.smcdel.txt` which describes the knowledge structure and the formulas you want to check for truth or validity:

    ```
    -- Three Muddy Children in SMCDEL
    VARS 1,2,3
    LAW  Top
    OBS  alice: 2,3
         bob:   1,3
         carol: 1,2
    WHERE?
      [ ! (1|2|3) ] alice knows whether 1
    VALID?
      [ ! (1|2|3) ]
      [ ! ((~ (alice knows whether 1)) & (~ (bob knows whether 2)) & (~ (carol knows whether 3))) ]
      [ ! ((~ (alice knows whether 1)) & (~ (bob knows whether 2)) & (~ (carol knows whether 3))) ]
      (alice,bob,carol) comknow that (1 & 2 & 3)
    ```

3) Run `smcdel MuddyShort.smcdel.txt` resulting in:

    ```
    >> smcdel MuddyShort.smcdel.txt
    SMCDEL 1.0 by Malvin Gattinger -- https://github.com/jrclogic/SMCDEL

    At which states is ... true?
    []
    [1]

    Is ... valid on the given structure?
    True
    ```

    More example files are in the folder [Examples](https://github.com/jrclogic/SMCDEL/tree/master/Examples).

4) To also build and install the web interface, run `stack install --flag smcdel:web`
   Then you can run `smcdel-web` and open <http://localhost:3000>.


## Advanced usage

The executables only provide model checking for S5 with public announcements.
For K and to define more complex models and updates, SMCDEL should be used as a Haskell library.
Please refer to the [Haddock documentation](https://hackage.haskell.org/package/smcdel) for each module.

Examples can be found in the folders
  [src/SMCDEL/Examples](https://github.com/jrclogic/SMCDEL/tree/master/src/SMCDEL/Examples)
and
  [bench](https://github.com/jrclogic/SMCDEL/tree/master/bench).

*Dependencies*:
To get all visualisation functions working, [graphviz](https://graphviz.org/), [dot2tex](https://github.com/kjellmf/dot2tex) and some LaTeX packages should be installed.
On Debian, please do `sudo apt install graphviz dot2tex libtinfo5 texlive-latex-base poppler-utils preview-latex-style texlive-pstricks zlib1g-dev`.


## Used BDD packages

SMCDEL uses different BDD packages.

- [Data.HasCacBDD](https://github.com/m4lvin/HasCacBDD) which runs CacBDD from <http://kailesu.net/CacBDD/>.
  This is the default choice used by the executables and the modules `Symbolic.S5` and `Symbolic.K`.

- The pure Haskell library [`decision-diagrams`](https://github.com/msakai/haskell-decision-diagrams).
  It is used by the module `Symbolic.S5_DD`.

- Optionally, [Cudd](https://github.com/davidcock/cudd) ([with some patches](https://github.com/m4lvin/cudd))
  which uses the CUDD library.
  To obtain the modules `SMCDEL.Symbolic.S5_CUDD`, `SMCDEL.Symbolic.S5_K`, `SMCDEL.Symbolic.S5_Ki`
  you should compile with `stack build --flag smcdel:with-cudd`.


## References

Main reference for the theory behind the implementation, also containing benchmarks:

- [Malvin Gattinger:
*New Directions in Model Checking Dynamic Epistemic Logic.*
PhD thesis, ILLC, Amsterdam,
2018](https://malv.in/phdthesis/).

Additional publications:

- [Johan van Benthem, Jan van Eijck, Malvin Gattinger, and Kaile Su:
*Symbolic Model Checking for Dynamic Epistemic Logic.*
In: Proceedings of The Fifth International Conference on Logic, Rationality and Interaction (LORI-V),
2015](https://doi.org/10.1007/978-3-662-48561-3_30).

- [Johan van Benthem, Jan van Eijck, Malvin Gattinger, and Kaile Su:
*Symbolic Model Checking for Dynamic Epistemic Logic --- S5 and Beyond.*
Journal of Logic and Computation,
2017](https://pure.uva.nl/ws/files/25483686/2016_05_23_del_bdd_lori_journal.pd.pdf).

- [Malvin Gattinger:
*Towards Symbolic Factual Change in DEL.*
ESSLLI 2017 student session,
2017](https://w4eg.de/malvin/illc/2017-07-symbolicfactualchange.pdf).

- [Daniel Miedema, Malvin Gattinger:
*Exploiting Asymmetry in Logic Puzzles: Using ZDDs for Symbolic Model Checking Dynamic Epistemic Logic*,
TARK 2023,
2023](https://doi.org/10.4204/EPTCS.379.32)
