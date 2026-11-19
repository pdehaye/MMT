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
| `PartialView.lean` | Partial morphisms and partial translation, preservation on the domain of definition, totality, composition, partial views in the module system | `api/modules/View.scala` (partial views) |
| `Diagrams.lean` | Diagrams; linear functors given by systematic renaming, with functor laws; connectors and naturality; sequencing, union, and connecting a diagram to its image | `api/modules/diagrams/{Diagram,LinearFunctor,LinearConnector,MetaOperators}.scala`, `SystematicRenamer` |
| `PushoutFunctor.lean` | The pushout functor along a meta-theory morphism `m : M → M'`: theories, morphisms, connectors, functor laws | `api/modules/diagrams/PushoutOperator.scala` (`PushoutFunctor`, `PushoutConnector`) |
| `Homomorphism.lean` | The homomorphism functor on first-order signatures over a logic `SFOL`: the theory `Hom(Σ)` of homomorphisms between two models, its well-formedness, its action on signature morphisms, and the projections | diagram operators (homomorphism functor) |
| `Checker.lean` | An executable type checker for LF (inference, checking with conversion, equality via δ, β and congruence) that returns a derivation with each answer, hence is sound by construction | `api/checking/{Solver,Rules}.scala`, `mmt-lf` rules |
| `Example.lean` | Worked examples over LF: the view `Magma → NatArith`, `Bimagma` with two structures `add, mul : Magma`, and runs of the checker. Each is checked and used to transport a typing derivation | — |

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
* Partial views:
  * `Term.ptrans_eq_some_iff`: partial translation is defined exactly on terms built
    from defined constants, and then equals the total translation;
  * `IsPartialMorphism.preserves`, `typing_ptrans`: judgments over the domain of
    definition are preserved;
  * `IsPartialMorphism.total_of_cover`, `of_total`: total and partial morphisms;
  * `IsPartialMorphism.comp`: partial morphisms compose;
  * `View.toPartial_total`, `View.WellTyped.toPartial`: module-level partial views.
* Diagram operators:
  * `LinFunctor.mor_isMorphism`: linear functors map well-typed morphisms to well-typed
    morphisms;
  * `LinFunctor.mor_id`, `LinFunctor.mor_comp`: the functor laws, as equations;
  * `LinFunctor.unit_isMorphism`, `LinFunctor.naturality`: the connector `S → F(S)` is
    a natural transformation;
  * `LinFunctor.comp_obj`, `comp_mor`: sequencing functors gives a functor;
  * `Diagram.map_wf`, `union_wf`, `connect_wf`: the operators preserve
    well-formedness of diagrams;
  * `Diagram.map_commutes`: they preserve commuting squares.
* Pushout functor:
  * `PFData.mor_isMorphism`: the induced morphism `P(σ) : P(S) → P(T)` is well-typed;
  * `PFData.naturality`: the connectors `S → P(S)` are natural;
  * `PFData.mor_id`, `PFData.mor_comp`: the functor laws, from the uniqueness part of
    the universal property;
  * `PFData.mor_meta`: `P(σ)` is the identity on `M'`.
* Homomorphism functor:
  * `Hom.homAx_typed`: each homomorphism axiom
    `f^h : Π x⃗:a⃗¹. ded (h_b (f¹ x⃗) = f² (h_{a₁} x₁) … (h_{aₙ} xₙ))` is well-typed in LF;
  * `Hom.homSig_wf`: every declaration of `Hom(Σ)` is well-typed;
  * `Hom.FOMor.hom_isMorphism`: `Hom(φ) : Hom(Σ) → Hom(Σ')` is a well-typed morphism;
  * `Hom.FOMor.hom_id`, `hom_comp`: the functor laws;
  * `Hom.proj_isMorphism`, `proj_naturality`: the projections `Σ → Hom(Σ)`, `c ↦ cᵏ`,
    are natural morphisms;
  * `Example.hom_op_typed`: the instance for magmas.
* Checker:
  * `LF.Checker.check_sound`, `eq_sound`: whatever the checker accepts is derivable;
  * `Example.check_conv`, `check_beta`, `reject_op_x`: runs of the checker, evaluated
    by `decide` in the kernel. They cover conversion via a definition, β-equality,
    and the rejection of an ill-typed term.

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
* A partial morphism is modelled as a total morphism out of its domain of definition.
  Judgments over the whole domain are not preserved in general, because their
  derivations may use undefined constants. MMT's option of expanding the definition
  of an unassigned defined constant is not modelled.
* Linear functors are modelled as systematic renamings. Each declaration yields one
  declaration whose type is translated along the renaming. This covers renaming and
  copying operators.
* The pushout functor applies to theories `S ⊇ M` whose declarations only refer to
  their own constants, and to morphisms that are the identity on `M`.
* The homomorphism functor is defined for first-order signatures (sorts and
  operations) over a logic meta-theory with `prop`, `ded` and polymorphic `eq`. Its
  action on morphisms covers signature morphisms, which send sorts to sorts and
  operations to operations with matching profiles. A view that sends an operation to
  a compound term would need `Hom(φ)` to send `f^h` to a *proof*, built by induction
  on that term from congruence rules of the logic. This is not covered.
* The checker is a model of the Solver's architecture, not a verification of the Scala
  code. It is sound by construction, since every answer carries its derivation. It
  works with fuel and gives no completeness guarantee.
* Not yet covered:
  * the homomorphism functor applied to views that send operations to compound terms,
    and to signatures beyond first-order ones (predicates, axioms, dependent types);
  * the meta-operators that select or rearrange theories (zipping, closure,
    difference, rebase);
  * the Solver's handling of unknowns: solving implicit arguments, delaying
    constraints, and type reconstruction;
  * completeness of the checker.
