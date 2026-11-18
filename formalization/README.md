# MMTFormal — a Lean 4 formalization of the MMT core

This directory formalizes the foundation-independent core of MMT, meaning its
term language and module system, in Lean 4. It does not depend on Mathlib.

```bash
cd formalization && lake build
```

The toolchain is pinned in `lean-toolchain` (Lean 4.36.0). The build contains no
`sorry`. The core theorems use only `propext` and `Quot.sound`. Flattening uses
classical logic.

## Contents

| File | Formalizes | Scala counterpart |
|---|---|---|
| `Term.lean` | Terms `var`/`const`/`app`/`bind`, de Bruijn shifting and substitution, closedness | `api/objects/Obj.scala` (`OMV`, `OMS`, `OMA`, `OMBIND`) |
| `Translation.lean` | Homomorphic translation along morphisms, identity, composition, functoriality, commutation with shifting and substitution | `Library.ApplyMorphs`, `api/objects/Translator.scala` |
| `Judgment.lean` | Flat signatures, judgments, abstract `Foundation`, derivability, well-typed morphisms, **judgment preservation**, category of theories | `api/checking/{Rules,Solver}.scala`, `api/objects/Judgements.scala` |
| `LF.lean` | LF as a concrete foundation, with proofs that its rules are stable under translation and context extension | `mmt-lf` |
| `Modules.lean` | Theories with meta-theories and includes, libraries, visibility, flattening, views, view checking | `api/modules/{Theory,View}.scala`, `api/symbols/{Constant,Structure}.scala` |
| `Example.lean` | Worked example: the view `Magma → NatArith` over LF, checked and used to transport a typing derivation | — |

## Main results

* `Term.trans_comp`, `Subst.comp_assoc`, `Term.trans_id`: translation is functorial.
* `Term.trans_inst`: translation commutes with substitution, `σ(t[u/x]) = σ(t)[σ(u)/x]`.
* `Derivable.trans` (**judgment preservation**): if `σ : S → T` is a well-typed
  morphism, then every judgment derivable over `S` translates to one derivable over `T`.
  This holds for any foundation whose rules are schematic.
* `IsMorphism.id`, `IsMorphism.comp`, `IsMorphism.incl`, and `Mor.comp_assoc` /
  `Mor.id_comp` / `Mor.comp_id`: theories and well-typed morphisms form a category,
  and inclusions are morphisms.
* `LF.foundation`: LF meets the foundation interface, so the preservation theorem
  applies to all LF-based theories.
* `Visible.isMorphism`: include and meta-theory paths are morphisms between flattenings.
* `View.isMorphism_of_check`: it is enough to check a view's assignments locally.
* `Example.natArith_plus_xx`: derives `x : N ⊢ plus x x : N` from
  `x : U ⊢ op x x : U` by applying the preservation theorem to the view.

## Modelling choices and scope

* Variables use de Bruijn indices. Binders bind one typed variable, and n-ary `OMA` is
  curried. Literals, attributions and semi-formal objects are left out, because
  translation does not act on them.
* A foundation is an abstract rule set with two closure properties:
  * stability under translations that are closed and fix the meta-symbols;
  * stability under outer context extension.

  MMT's design relies on both of these without stating them.
* Constants come with optional types and definitions. The module system adds the lookup
  rule `c : A` and the definition rule `c ≡ d : A`.
* Global names are qualified by their home theory. So flattening is a lookup filtered by
  visibility and needs no renaming.
* Not yet covered: structures with assignments and their pushouts, partial views,
  the diagram operators (`modules/diagrams`), and the soundness of MMT's checking
  algorithm (`Solver`) with respect to the declarative judgments formalized here.
