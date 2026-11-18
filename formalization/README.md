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
| `Modules.lean` | Theories with meta-theories, includes and structure declarations; libraries, visibility, flattening (including structure copies), views, view checking, structure morphisms | `api/modules/{Theory,View}.scala`, `api/symbols/{Constant,Structure}.scala` |
| `Pushout.lean` | Pushout of a theory extension `S ⊆ S'` along a morphism `σ : S → T`, with fresh renaming and assignments; its universal property; structures as pushouts along the meta-theory | `api/symbols/Structure.scala`, `api/modules/diagrams/PushoutOperator.scala` |
| `StructurePushout.lean` | Flattening a theory with a structure declaration is the pushout of `Pushout.lean`, and the structure morphism is the pushout morphism | `api/symbols/Structure.scala` |
| `Example.lean` | Worked examples over LF: the view `Magma → NatArith`, and `Bimagma` with two structures `add, mul : Magma`. Each is checked and used to transport a typing derivation | — |

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
* `structMor_isMorphism`, `structMor_preserves`: a `structure s : S` declared in a
  theory `H` induces a well-typed morphism `flat S → flat H`. It sends shared
  constants to themselves and the others to their copies `H?s/c`.
* `flat_struct_eq_pushout`: if `H` declares `structure s : Sdom`, then `flat H` *is* the
  pushout of `flat Sdom` along the identity on the constants shared with `H`. The base
  of the pushout is `H` without the copies made by `s`. `poMor_eq_structMor` shows that
  the pushout morphism coincides with `structMor` on `Sdom`.
* `flat_struct_universal`: so the host theory has the universal property of a pushout,
  with the structure morphism as one of its legs.
* `pushout_isMorphism`, `pushout_incl`, `pushout_commutes`: the pushout square of
  well-typed morphisms. `σ' : S' → T'` is well-typed, `T ⊆ T'`, and `σ'` agrees with
  `σ` on `S`.
* `pushout_universal`: every cocone `τ : T → U`, `μ : S' → U` with `μ|S = σ;τ` that
  respects the assignments factors through a well-typed mediating morphism `T' → U`.
  That morphism is unique on the constants of `T'`.
* `Structure.isMorphism`, `Structure.preserves`: an MMT structure `s : S` in `T` induces a
  well-typed morphism `S → T'`. Every judgment of `S` holds in `T'` after renaming.
* `Example.natArith_plus_xx`: derives `x : N ⊢ plus x x : N` from
  `x : U ⊢ op x x : U` by applying the preservation theorem to the view.
* `Example.bimagma_addop_xx`: the same derivation, transported along the structure
  `add`, gives `x : add/U ⊢ add/op x x : add/U` in `Bimagma`.

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
* Local names are either base names or structure copies `LName.sub s S c`, MMT's
  complex names `[S]/s/c`. The declaration of a copy is computed by recursion on its
  local name: it is the original declaration, translated along the structure.
* In the module layer, a structure shares the constants that are already visible in
  the host, such as the meta-theory, and copies all the others.
* Pushouts and structures are built on flat signatures. The fresh names (MMT's
  `T?s/c`) come from an abstract injective `Renaming`. Assignments may only define
  copied constants that have no definiens. The universal property assumes that the
  host and the extension are closed, i.e. their declarations refer only to their own
  constants.
* Not yet covered:
  * partial views;
  * the remaining diagram operators (`modules/diagrams`);
  * the soundness of MMT's checking algorithm (`Solver`) with respect to the
    declarative judgments formalized here.
