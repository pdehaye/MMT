import MMTlib.Core.Term
import MMTlib.Core.Translation
import MMTlib.Core.Judgment
import MMTlib.Core.FoundationMorphism
import MMTlib.Foundations.LF.Basic
import MMTlib.Foundations.LF.Meta
import MMTlib.Foundations.STLC.Basic
import MMTlib.Foundations.STLC.ToLF
import MMTlib.Modules.Basic
import MMTlib.Modules.Pushout
import MMTlib.Modules.StructurePushout
import MMTlib.Modules.PartialView
import MMTlib.Diagrams.Basic
import MMTlib.Diagrams.MetaOperators
import MMTlib.Diagrams.PushoutFunctor
import MMTlib.Diagrams.Homomorphism.Basic
import MMTlib.Diagrams.Homomorphism.Views
import MMTlib.Checking.TypeChecker
import MMTlib.Checking.Completeness
import MMTlib.Checking.Unknowns
import MMTlib.Checking.ModuleChecker

/-!
# MMTlib

A Lean 4 formalization of the MMT language and system. See `README.md` for an overview
and the correspondence with MMT's Scala sources.

* `MMTlib.Core`: terms, translation along morphisms, judgments over an abstract
  foundation, judgment preservation, foundation morphisms.
* `MMTlib.Foundations`: LF (with its metatheory) and the simply typed λ-calculus.
* `MMTlib.Modules`: theories, includes, structures, views, pushouts, partial views.
* `MMTlib.Diagrams`: diagram operators (renaming, pushout and homomorphism functors,
  meta-operators).
* `MMTlib.Checking`: executable checkers proved sound, unknowns, type reconstruction.

All declarations live in the namespace `MMT`.
-/
