# Changelog

## Unreleased

* The homomorphism functor for signatures with predicates
  (`MMTlib.Diagrams.Homomorphism.Predicates`): preservation axioms
  `p^h : Π x⃗. ded (p¹ x⃗) → ded (p² (h x⃗))`, well-formedness, and functoriality for
  morphisms mapping predicates to predicates.

## 0.1.0

First release of MMTlib as a Lean library, reorganized from the `formalization/`
directory (`MMTFormal`) into the module hierarchy `MMTlib.{Core, Foundations, Modules,
Diagrams, Checking}` with a separate examples library `MMTlibExamples`, run by
`lake test`.

* Core: terms, translation, judgments over abstract foundations, judgment preservation,
  the category of theories, foundation morphisms.
* Foundations: LF (scoping, weakening, substitution) and STLC, with the embedding of
  STLC into LF.
* Module system: includes, structures, views, flattening, pushouts (structures are
  pushouts), partial views.
* Diagram operators: renaming, pushout and homomorphism functors (the latter also on
  compound-term views), meta-operators.
* Checking: sound LF type checker, complete for syntax-directed typing; unknowns,
  unification and type reconstruction; verified theory and view checkers.
* Package options: `autoImplicit := false`; CI with `--wfail` and an axiom audit.
