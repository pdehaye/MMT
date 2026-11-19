# Changelog

## Unreleased

* Weakening and the substitution lemma are proved once for every foundation with
  stable rules (`MMTlib.Core.Structural`); LF and STLC instantiate them
  (`MMTlib.Foundations.STLC.Meta` is new, with inversion and subject reduction). The
  generic de Bruijn identities moved from `LF.Meta` to `Core.Structural` (names unchanged).
* Delayed constraints (`MMTlib.Checking.DelayedConstraints`): unification up to β by
  normalization, solving passes that delay constraints until they become solvable.
* Higher-order pattern unification (`MMTlib.Checking.PatternUnification`): solutions
  `?X := λy⃗. t[y⃗/x⃗]`, sound up to β-reduction; constraints solved up to β, then the
  instance is checked.
* Confluence of β-reduction (`MMTlib.Foundations.LF.Confluence`): parallel
  reduction, complete development, the Church–Rosser theorem, uniqueness of normal
  forms, and conversion as joinability; morphisms preserve reduction.
* An executable β-conversion check (`MMTlib.Checking.BetaConversion`), correct in both
  directions by confluence; `Normal` is decidable.
* Docstrings for every public declaration, enforced by `linter.missingDocs`.

* The homomorphism functor for signatures with predicates
  (`MMTlib.Diagrams.Homomorphism.Predicates`): preservation axioms
  `p^h : Π x⃗. ded (p¹ x⃗) → ded (p² (h x⃗))`, well-formedness, and functoriality for
  morphisms mapping predicates to predicates.
* The homomorphism functor for equational theories
  (`MMTlib.Diagrams.Homomorphism.Axioms`): copies `axᵏ : Π x⃗. ded (sᵏ = tᵏ)` of the
  axioms in both models, well-formedness, and functoriality for morphisms mapping
  axioms to axioms.

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
