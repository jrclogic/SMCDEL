# SMCDEL Changelog

## upcoming

New:

- "TRUE?" command in Web and CI interface
- multipointed translations
- optimization of symbolic structures

Changed:

- improve test coverage
- new definitions and functions for `MultipointedEvent = (Transformer,Bdd)`
- swapped argument order of `icSolves`
- use HasCacBDD-0.1.0.3
- update ace.js and MathJax
- check if dot2tex is available before using it


## v1.1.0 (2019-12-09)

New:

- minimization under bisimulation
- dynamic operators in formulas via `Data.Dynamic`
- multipointed models, action models, structures and events
- added Cheryl's Birthday and Cheryl's Age examples
- experimental functions for epistemic planning (with small examples)
- more instances for QuickCheck, more tests
- add S5 to K conversion in `SMCDEL.Translations.Convert`
- improvements to the web interface

Changed:

- polymorphic `update` replaces `productUpdate`, `transform`, `pubAnnounce` etc.
- factual change by default: merge `Symbolic.S5.Change` into `Symbolic.S5` etc.
- remove changeprops in (Kn)Trf to avoid redundancy with changelaw
- move BDD related functions to HasCacBDD (`substit`, `substitSimul`)
- avoid `Data.Map` in S5 modules, no longer depend on `lens`
- replace `.cabal` file with a `package.yml` for `hpack`


## v1.0.0  (2018-02-26)

New:

- action models and transformers with factual change
- NonS5 modules, now called K, are no longer experimental
- separate types State and World
- automated testing and benchmarks
- lots of bugfixes

Removed:

- removed support for robbed, NooBDD and Z3
- old Example files


## v0.2  (2015-11-17)

First release with a standalone-executable.


## v0.1  (2015-09-21)

The first public version of SMCDEL. Note that this version does not contain a
stand-alone executable. It can only be used as a Haskell library.
