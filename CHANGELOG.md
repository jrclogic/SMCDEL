# SMCDEL Changelog

## upcoming

New:

- minimization via bisimulation
- multipointed models, action models, structures and events
- added Cheryl's Birthday example

Changed:

- polymorphic `update` replaces `productUpdate`, `transform`, `pubAnnounce` etc.
- factual change per default: merge `Symbolic.S5.Change` into `Symbolic.S5` etc.
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
