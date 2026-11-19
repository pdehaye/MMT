# MMTlib — a Lean 4 formalization of MMT

MMTlib is a Lean 4 library formalizing MMT, without dependencies (no Mathlib). It covers:
* the foundation-independent core (terms, morphisms, judgments);
* two foundations, LF and the simply typed λ-calculus, and foundation morphisms;
* the metatheory of LF, including confluence of β-reduction;
* the module system (theories, includes, structures, views, partial views) and pushouts;
* diagram operators;
* executable checkers that are proved sound: a type checker, a theory checker and a
  view checker, plus unknowns with unification and type reconstruction.

```bash
cd MMTlib
lake build          # the library
lake test           # the examples and the axiom audit
lake build --wfail  # as CI does: warnings (including `sorry`) are errors
```

The toolchain is pinned in `lean-toolchain` (Lean 4.36.0). The build contains no
`sorry`. The theorems use only Lean's standard axioms (`propext`, `Quot.sound`, and
`Classical.choice` where flattening decides visibility classically). Computational
examples are evaluated by `decide` in the kernel.

## Using MMTlib

Add it to another Lake project with

```toml
[[require]]
name = "MMTlib"
git = "https://github.com/pdehaye/MMT"
subDir = "MMTlib"
rev = "<commit>"
```

and `import MMTlib` (or individual modules such as `import MMTlib.Modules.Basic`).

## Conventions

* All declarations live in the namespace `MMT`; sub-namespaces follow the topic (`MMT.LF`,
  `MMT.STLC`, `MMT.Hom`, `MMT.LF.Checker`, …).
* `autoImplicit` and `relaxedAutoImplicit` are off for the whole package.
* Every module starts with a module docstring stating what it formalizes and its main
  results. Every public definition, structure field and constructor has a docstring,
  enforced by `linter.missingDocs` (warnings fail CI).
* Computational facts are checked by `decide`, in the kernel, never by `native_decide`.
* The library builds without warnings; CI (`.github/workflows/mmtlib.yml`) builds with
  `--wfail` and runs `lake test`, whose axiom audit (`MMTlibExamples.Axioms`) fails if a
  main theorem acquires a new axiom.

## Contents

| Module | Formalizes | Scala counterpart |
|---|---|---|
| **Core** | | |
| `MMTlib.Core.Term` | Terms `var`/`const`/`app`/`bind`, de Bruijn shifting and substitution, closedness | `api/objects/Obj.scala` (`OMV`, `OMS`, `OMA`, `OMBIND`) |
| `MMTlib.Core.Translation` | Homomorphic translation along morphisms, functoriality, commutation with shifting and substitution | `Library.ApplyMorphs`, `api/objects/Translator.scala` |
| `MMTlib.Core.Judgment` | Flat signatures, judgments, abstract `Foundation`, derivability, well-typed morphisms, **judgment preservation**, category of theories | `api/checking/{Rules,Solver}.scala`, `api/objects/Judgements.scala` |
| **Foundations** | | |
| `MMTlib.Foundations.LF.Basic` | LF as a foundation; its rules are stable under translation and context extension | `mmt-lf` |
| `MMTlib.Foundations.LF.Meta` | Metatheory of LF: de Bruijn identities, scoping, inner weakening, substitution lemma | `mmt-lf` |
| `MMTlib.Foundations.LF.Confluence` | β-reduction, parallel reduction, complete development; Church–Rosser, unique normal forms | `mmt-lf` (`Beta` rule) |
| `MMTlib.Core.FoundationMorphism` | Foundation morphisms and the transport of derivations | meta-theory morphisms |
| `MMTlib.Foundations.STLC.Basic` | A second foundation, the simply typed λ-calculus | foundation-independence |
| `MMTlib.Foundations.STLC.ToLF` | The embedding of STLC into LF | meta-theory morphisms |
| **Module system** | | |
| `MMTlib.Modules.Basic` | Theories with meta-theories, includes and structures; visibility; flattening (including structure copies); views; structure morphisms | `api/modules/{Theory,View}.scala`, `api/symbols/{Constant,Structure}.scala` |
| `MMTlib.Modules.Pushout` | Pushout of a theory extension along a morphism, with renaming and assignments; universal property; structures as pushouts | `api/symbols/Structure.scala`, `PushoutOperator.scala` |
| `MMTlib.Modules.StructurePushout` | Flattening a structure declaration is literally that pushout | `api/symbols/Structure.scala` |
| `MMTlib.Modules.PartialView` | Partial morphisms, partial translation, preservation, totality, composition, partial views | `api/modules/View.scala` |
| **Diagram operators** | | |
| `MMTlib.Diagrams.Basic` | Diagrams; linear functors by systematic renaming; functor laws; connectors; composition, union, connect | `api/modules/diagrams/{Diagram,LinearFunctor,LinearConnector}.scala`, `SystematicRenamer` |
| `MMTlib.Diagrams.MetaOperators` | Meta-operators: union, difference, rebase, subsumption, closure; sequencing and zipping | `api/modules/diagrams/{Diagram,MetaOperators,ZippingOperator}.scala` |
| `MMTlib.Diagrams.PushoutFunctor` | The pushout functor along a meta-theory morphism | `PushoutOperator.scala` (`PushoutFunctor`, `PushoutConnector`) |
| `MMTlib.Diagrams.Homomorphism.Basic` | The homomorphism functor on first-order signatures: `Hom(Σ)`, its well-formedness, its action on signature morphisms, the projections | diagram operators (homomorphism functor) |
| `MMTlib.Diagrams.Homomorphism.Predicates` | The homomorphism functor for signatures with predicates: preservation axioms, well-formedness, functoriality | diagram operators (homomorphism functor) |
| `MMTlib.Diagrams.Homomorphism.Axioms` | The homomorphism functor for equational theories: copies of the axioms in both models, well-formedness, functoriality | diagram operators (homomorphism functor) |
| `MMTlib.Diagrams.Homomorphism.Views` | The homomorphism functor on views that send operations to compound terms | diagram operators (homomorphism functor) |
| **Checking** | | |
| `MMTlib.Checking.TypeChecker` | An executable LF type checker (inference, checking with conversion, equality via δ, β and congruence) that returns a derivation with each answer | `api/checking/{Solver,Rules}.scala` |
| `MMTlib.Checking.BetaConversion` | Executable normal-order β-normalizer; conversion check that is correct in both directions, by confluence | `api/checking/Solver.scala` (equality check) |
| `MMTlib.Checking.Completeness` | Completeness of the checker for syntax-directed typing | `api/checking/Solver.scala` |
| `MMTlib.Checking.Unknowns` | Unknowns: solutions as morphisms, unification, solved unknowns as definitions, type reconstruction | `api/checking/Solver.scala` |
| `MMTlib.Checking.DelayedConstraints` | Delayed constraints: unification up to β by normalization, passes that delay unsolvable constraints, solving then checking | `api/checking/Solver.scala` (delayed constraints) |
| `MMTlib.Checking.PatternUnification` | Higher-order pattern unification `?X x⃗ ≐ t`, sound up to β; solving then checking | `api/checking/Solver.scala` (`solveVariable`) |
| `MMTlib.Checking.ModuleChecker` | Executable theory and view checkers over a library; computable visibility and flattening | `api/checking/MMTStructureChecker.scala` |
| **Examples** | | |
| `MMTlibExamples.Algebra` | Magmas, natural numbers, `Bimagma` with two structures; transport along a view and a structure | — |
| `MMTlibExamples.TypeChecker` | Runs of the type checker | — |
| `MMTlibExamples.ModuleChecker` | Runs of the theory and view checkers | — |
| `MMTlibExamples.Homomorphism` | `Hom(Magma)`; `Hom` of a compound-term view | — |
| `MMTlibExamples.Unknowns` | Implicit arguments | — |
| `MMTlibExamples.PatternUnification` | Solving `?F x ≐ succ x` by `?F := λx. succ x` | — |
| `MMTlibExamples.DelayedConstraints` | `?F ?A ≐ c` delayed until `?F` is solved | — |
| `MMTlibExamples.Reduction` | β-reduction of the K combinator; its unique normal form; conversion checks by `decide` | — |
| `MMTlibExamples.STLC` | An STLC derivation read in LF | — |
| `MMTlibExamples.Axioms` | Axiom audit of the main theorems (`#guard_msgs`) | — |

## Main results

### Core

* `Term.trans_comp`, `Subst.comp_assoc`, `Term.trans_id`: translation is functorial.
* `Term.trans_inst`: translation commutes with substitution, `σ(t[u/x]) = σ(t)[σ(u)/x]`.
* `Derivable.trans` (**judgment preservation**): a well-typed morphism `σ : S → T` maps
  every judgment derivable over `S` to one derivable over `T`, for any foundation whose
  rules are schematic.
* `IsMorphism.id`, `IsMorphism.comp`, `IsMorphism.incl`, `Mor.comp_assoc`,
  `Mor.id_comp`, `Mor.comp_id`: theories and well-typed morphisms form a category, and
  inclusions are morphisms.

### Foundations and the metatheory of LF

* `LF.foundation`: LF meets the foundation interface.
* `LF.scoping`: in a derivable judgment, all terms use only variables of the context.
  So checked declarations are closed (`DeclOK.closed`).
* `LF.weaken`: inner weakening. A variable can be inserted at any position of the
  context.
* `LF.subst`: the substitution lemma. If `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
  `Δ[u/x], Γ ⊢ J[u/x]`. Both lemmas assume the signature's declarations are closed.
* `LF.Red.confluent` (**Church–Rosser**): β-reduction is confluent, by the
  Tait–Martin-Löf method with Takahashi's complete development (`LF.Par.triangle`,
  `LF.Par.diamond`). Consequences: `LF.Red.normal_unique` (normal forms are unique) and
  `LF.Conv.joinable` (β-convertible terms have a common reduct). `LF.Red.trans`:
  morphisms that fix `λ` preserve reduction and conversion.
* `LF.conv?_correct`: the executable conversion check, comparing normal forms, is
  sound and complete whenever both terms normalize within the fuel.
* `STLC.foundation`: the simply typed λ-calculus is a second foundation, so all
  generic results apply to it.
* `FMor.preserves`: a *foundation morphism* translates terms so that every source rule
  is derivable in the target. It transports every derivation.
* `stlcToLF`: STLC embeds into LF (`tp ↦ type`, `→ ↦ Π`, `λ ↦ λ`), using weakening in LF;
  `STLC.Example.ssz_LF` reads an STLC derivation in LF.

### Module system

* `Visible.isMorphism`: include and meta-theory paths are morphisms between flattenings.
* `View.isMorphism_of_check`: it is enough to check a view's assignments locally.
* `structMor_isMorphism`, `structMor_preserves`: a `structure s : S` declared in `H`
  induces a well-typed morphism `flat S → flat H`. Shared constants go to themselves,
  the others to their copies `H?s/c`.
* `pushout_isMorphism`, `pushout_incl`, `pushout_commutes`, `pushout_universal`: the
  pushout square and its universal property. The mediating morphism exists and is
  unique on the constants of the pushout.
* `flat_struct_eq_pushout`, `poMor_eq_structMor`, `flat_struct_universal`: flattening a
  structure declaration *is* the pushout, and the structure morphism is the pushout
  morphism.
* Partial views:
  * `Term.ptrans_eq_some_iff`: partial translation is defined exactly on terms built
    from defined constants;
  * `IsPartialMorphism.preserves`: judgments over the domain of definition are
    preserved;
  * `total_of_cover`, `of_total`: totality;
  * `IsPartialMorphism.comp`: composition;
  * `View.WellTyped.toPartial`: partial views in the module system.

### Diagram operators

* Renaming functors:
  * `LinFunctor.mor_isMorphism`: they preserve well-typed morphisms;
  * `mor_id`, `mor_comp`: the functor laws, as equations;
  * `unit_isMorphism`, `naturality`: the connectors are natural;
  * `comp_obj`, `comp_mor`: functors compose;
  * `Diagram.map_wf`, `union_wf`, `connect_wf`, `map_commutes`: well-formedness and
    commuting squares are preserved.
* Meta-operators:
  * membership lemmas for union, difference and rebase;
  * `union_subsumes_left`, `union_subsumes_right`: the union subsumes both arguments;
  * `closure_iff`: MMT's iterative closure computes exactly the least set of theories
    reachable by includes and structures outside the meta-diagram;
  * `closure_complete`: the closure together with its meta-diagram is closed under
    dependencies;
  * `sequenced_wf`, `zipped_wf`: sequencing and zipping preserve well-formedness.
* Pushout functor: `PFData.mor_isMorphism`, `naturality`, `mor_id`, `mor_comp`,
  `mor_meta`.
* Homomorphism functor:
  * `Hom.homAx_typed`, `homSig_wf`: every declaration of `Hom(Σ)` is well-typed,
    including the axioms `f^h : Π x⃗. ded (h_b (f¹ x⃗) = f² (h x⃗))`;
  * `Hom.FOMor.hom_isMorphism`, `hom_id`, `hom_comp`: functoriality on signature
    morphisms;
  * `Hom.proj_isMorphism`, `proj_naturality`: the projections `Σ → Hom(Σ)` are natural
    morphisms;
  * `Hom.predAx_typed`, `homSigP_wf`, `FOMorP.hom_isMorphism`, `FOMorP.hom_comp`:
    with predicates `p : a⃗`, `Hom(Σ)` declares the preservation axioms
    `p^h : Π x⃗. ded (p¹ x⃗) → ded (p² (h x⃗))`. Everything is well-typed, and morphisms
    that map predicates to predicates induce well-typed morphisms. The extension is
    conservative (`homSig_sub_homSigP`);
  * `Hom.eqAx_typed`, `homSigA_wf`, `FOMorA.hom_isMorphism`: for equational theories,
    `Hom(Σ)` contains the copies `axᵏ : Π x⃗. ded (sᵏ = tᵏ)` of every axiom in both
    models. Everything is well-typed, and morphisms mapping axioms to axioms induce
    well-typed morphisms;
  * `Hom.FOView.hom_isMorphism`: for views that send operations to compound terms
    `λx⃗. t`, `Hom(φ)` is well-typed. It sends `f^h` to a proof `λx⃗. P(t)` built from
    `g^h`, `refl`, `trans` and `cong` (`proofP_typed`), moved to the translated axiom by
    multi-step β-conversion (`multiBeta`, `proofP_converted`).

### Checking

* `LF.Checker.check_sound`, `eq_sound`: whatever the type checker accepts is
  derivable.
* `LF.Checker.infer_complete`, `check_complete`: the checker is complete for
  syntax-directed typing (`Alg`).
* Unknowns:
  * `solution_transport`: a well-typed solution is a morphism from the signature
    extended by the unknowns, so everything derived with unknowns holds after
    instantiation;
  * `unify_sound`: first-order unification is sound;
  * `checkSolved_sound`: solved unknowns as definitions, unfolded by δ;
  * `elaborate_sound`: type reconstruction. Untrusted constraint generation,
    unification, then a trusted check.
  * `patSol_red`, `solveCheckP_sound`: higher-order pattern unification. The solution
    `?X := λy⃗. t[y⃗/x⃗]` satisfies `?X x⃗ ≐ t` up to β; after solving, the instance is
    checked by the sound checker.
  * `solveDelayed_sound`, `solveCheckD_sound`: delayed constraints. Constraints that
    cannot be solved yet are retried after the others. Constraints solved early stay
    solved, because solutions preserve β-conversion.
* Computable flattening: `visDec_iff`, `flatB_sub`, `flatB_eq`. Visibility is decidable
  under a decidable completeness certificate. The computable flattening, including
  structure copies, is sound, and exact under the certificates.
* `checkTheory_sound`: an accepted theory is well-formed, declaration by declaration
  (`TheoryWF`). Constants are typed. For structures (`StructOK`), the induced morphism is
  well-typed and the assignments are typed.
* `checkView_sound`: an accepted view is a well-typed morphism. Structures may occur in
  the codomain and in the domain.

### Examples (`MMTlibExamples`)

* Transport along a view and a structure: `natArith_plus_xx`, `bimagma_addop_xx`.
* Type checker: `check_conv`, `check_beta`, `reject_op_x`.
* Theory checker:
  * `magma_checks`, `natArith_checks`, `bimagma_checks`: theories are accepted;
  * `magmaN_checks`: a structure with an assignment is accepted;
  * `bimagmaExt_checks`: a theory using structure copies is accepted;
  * `bad_rejected`, `magmaBad_rejected`: a use before declaration and an ill-typed
    assignment are rejected.
* View checker:
  * `plusView_checks`: the view `Magma → NatArith`, replacing the hand proof
    `plusView_wellTyped`;
  * `addView_checks`: a view into `Bimagma`, through the structure copies;
  * `bimagmaView_checks`: a view out of `Bimagma`;
  * `badView_rejected`, `bimagmaViewPartial_rejected`: an ill-typed view and an
    incomplete view are rejected.
* Homomorphism functor:
  * `hom_op_typed`: `Hom(Magma)`;
  * `hom_plusZeroView`: the view `op ↦ λx y. plus x (plus y zero)`;
  * `hom_le_typed`: ordered magmas, with the predicate `le`;
  * `hom_assoc_typed`: semigroups, with associativity.
* Unknowns: the implicit argument of `id ?A c : N`, solved by unification
  (`idApp_solved`), as a solved definition (`idApp_checkSolved`), and by
  reconstruction (`idApp_reconstructed`). A higher-order pattern `?F x ≐ succ x`
  (`MMTlibExamples.PatternUnification`). A constraint `?F ?A ≐ c` that must be delayed
  (`MMTlibExamples.DelayedConstraints`).

## Modelling choices and scope

* Variables use de Bruijn indices. Binders bind one typed variable, and n-ary `OMA` is
  curried. Literals, attributions and semi-formal objects are left out, because
  translation does not act on them.
* A foundation is an abstract rule set with two closure properties:
  * stability under translations that are closed and fix the meta-symbols;
  * stability under outer context extension.

  MMT's design relies on both of these without stating them.
* Constants have optional types and definitions. The module system adds the rules
  `c : A` and `c ≡ d : A`.
* Global names are qualified by their home theory, so flattening is a lookup filtered
  by visibility. Local names are base names or structure copies `LName.sub s S c`,
  MMT's complex names. A structure shares the constants already visible in the host
  and copies the others.
* Pushouts on flat signatures use an abstract injective renaming for fresh names.
  Assignments only define copied constants without definiens. The universal property
  assumes closed signatures.
* A partial morphism is modelled as a total morphism out of its domain of definition.
  MMT's option of expanding the definition of an unassigned defined constant is not
  modelled.
* Linear functors are modelled as systematic renamings, each declaration yielding one
  declaration. The pushout and homomorphism functors are formalized separately.
* The homomorphism functor works on first-order signatures (sorts, operations,
  predicates and equational axioms) over
  a logic meta-theory `SFOL` with `prop`, `ded`, polymorphic `eq`, `refl`, `trans` and
  `cong`. For compound-term views, the functor laws hold only up to equality of proofs.
* `MMTlib.Diagrams.Homomorphism.Views` predates the substitution lemma. It keeps intermediate terms as
  encodings of first-order terms under variable-like valuations, and types them
  directly.
* In the LF rule for Π-congruence, the universe of the codomain premise is lifted
  (`U.liftN 1 0`), as de Bruijn indexing requires.
* The checkers model MMT's architecture; they are not a verification of the Scala
  code. The type checker is sound by construction (every answer carries its
  derivation), uses fuel, and is complete for syntax-directed typing. The theory and
  view checkers:
  * require visibility certificates;
  * allow structures in the codomain of a view and in its domain, but the domain's
    structures must have structure-free domains, and the other visible theories must
    declare no structures;
  * require structure assignments to define base constants without definiens.

  Other inputs are rejected (soundly).

## Not yet covered

* The homomorphism functor for axioms beyond equations (which need logical
  connectives), for dependent types, and for compound-term views of signatures with
  predicates or axioms. Its functor laws for compound-term views, which hold only up to
  proof irrelevance.
* Most-generality of pattern unification, and the Solver's other strategies (type-directed
  rules, η, unknowns in contexts).
* Completeness of the checker with conversion. Confluence of β-reduction is proved;
  normalization of well-typed terms and subject reduction are not.

## License

MMTlib is part of the MMT repository, and the repository's license (`COPYING.txt`)
applies.
