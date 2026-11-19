import MMTFormal.Pushout

/-!
# The pushout functor

MMT's `PushoutFunctor` (`api/modules/diagrams/PushoutOperator.scala`) translates a
whole diagram of theories along a morphism of their common meta-theory
`m : M → M'`. Each theory `S ⊇ M` becomes its pushout `P(S)` along `m`. Each
morphism `σ : S → T` that is the identity on `M` becomes the induced morphism
`P(σ) : P(S) → P(T)`. Each theory is connected to its image by the pushout morphism
`S → P(S)`, which is MMT's `PushoutConnector`.

Main results:
* `PFData.mor_isMorphism`: `P(σ)` is a well-typed morphism.
* `PFData.naturality`: the connectors `S → P(S)` form a natural transformation.
* `PFData.mor_id`, `PFData.mor_comp`: the functor laws hold on the constants of
  `P(S)`. They follow from the uniqueness part of the universal property.
* `PFData.mor_meta`: `P(σ)` is the identity on the new meta-theory `M'`.
-/

namespace MMT

/-- Translation preserves "uses only" along a substitution. -/
theorem Term.UsesOnly.trans' {P Q : GName → Prop} {σ : Subst} {x : Term}
    (hx : x.UsesOnly P) (hσ : ∀ c, P c → (σ c).UsesOnly Q) : (x.trans σ).UsesOnly Q := by
  induction x with
  | var => trivial
  | const c => exact hσ c hx
  | app f a ihf iha => exact ⟨ihf hx.1, iha hx.2⟩
  | bind b A t ihb ihA iht => exact ⟨ihb hx.1, ihA hx.2.1, iht hx.2.2⟩

/-- The data of a pushout functor: a morphism `m : M → M'` of meta-theories and a
renaming for the copied constants. -/
structure PFData (F : Foundation) where
  M : Sig
  M' : Sig
  m : Subst
  ρ : Renaming
  hm : IsMorphism F M M' m
  closedM : M.Closed
  closedM' : M'.Closed
  land : m.LandsIn M M'
  fresh : ∀ c, M' (ρ.fwd c) = none
  metaFwd : ∀ c, ¬ F.metaSym (ρ.fwd c)

namespace PFData

variable {F : Foundation} (P : PFData F)

/-- A theory over the meta-theory `M`. -/
structure Thy where
  S : Sig
  sub : P.M.Sub S
  closed : S.Closed
  metaNew : ∀ c, isNew P.M S c = true → ¬ F.metaSym c

/-- A morphism of theories over `M`: well-typed, the identity on `M`, and mapping to
terms over the codomain. -/
structure Hom (A B : P.Thy) (σ : Subst) : Prop where
  mor : IsMorphism F A.S B.S σ
  fixM : ∀ c, P.M.Has c → σ c = .const c
  lands : σ.LandsIn A.S B.S

variable {P}

/-- Action on theories: the pushout along `m`. -/
def obj (A : P.Thy) : Sig := poSig P.M A.S P.M' P.m P.ρ (fun _ => none)

/-- The connector `S → P(S)`. -/
def unit (A : P.Thy) : Subst := poMor P.M A.S P.m P.ρ

/-- Action on morphisms: the mediating morphism of the pushout. -/
def mor (A B : P.Thy) (σ : Subst) : Subst :=
  poMed P.M A.S P.M' Subst.id (σ.comp (unit B)) P.ρ

theorem hyp (A : P.Thy) : PushoutHyp F P.M A.S P.M' P.m P.ρ (fun _ => none) where
  sub := A.sub
  mor := P.hm
  closedS := P.closedM
  fresh := P.fresh
  metaNew := A.metaNew
  metaFwd := P.metaFwd
  assignOk _ _ h := by cases h

/-- The connector is a well-typed morphism. -/
theorem unit_isMorphism (A : P.Thy) : IsMorphism F A.S (obj A) (unit A) :=
  pushout_isMorphism (hyp A)

theorem unit_M (A : P.Thy) {c : GName} (h : P.M.Has c) : unit A c = P.m c :=
  pushout_commutes h

/-- The universal property, specialized to the cocone `(M' ⊆ P(T), σ ; unit)`. -/
theorem univ {A B : P.Thy} {σ : Subst} (hσ : P.Hom A B σ) :
    IsMorphism F (obj A) (obj B) (mor A B σ) ∧
    (∀ d, P.M'.Has d → mor A B σ d = Subst.id d) ∧
    (∀ c, A.S.Has c → (unit A c).trans (mor A B σ) = (σ.comp (unit B)) c) ∧
    (∀ u : Subst, (∀ d, P.M'.Has d → u d = Subst.id d) →
      (∀ c, A.S.Has c → (unit A c).trans u = (σ.comp (unit B)) c) →
      ∀ d, (obj A).Has d → u d = mor A B σ d) :=
  pushout_universal (hyp A) P.land P.closedM' A.closed
    (τ := Subst.id) (μ := σ.comp (unit B)) (U := obj B)
    (IsMorphism.incl pushout_incl) (hσ.mor.comp (unit_isMorphism B))
    (fun c hc => by
      simp [Subst.comp, hσ.fixM c hc, Term.trans, unit_M B hc])
    (fun _ _ _ h => by cases h)

/-- `P(σ)` is a well-typed morphism. -/
theorem mor_isMorphism {A B : P.Thy} {σ : Subst} (hσ : P.Hom A B σ) :
    IsMorphism F (obj A) (obj B) (mor A B σ) :=
  (univ hσ).1

/-- `P(σ)` is the identity on `M'`. -/
theorem mor_meta {A B : P.Thy} {σ : Subst} (hσ : P.Hom A B σ) {d : GName} (h : P.M'.Has d) :
    mor A B σ d = .const d :=
  (univ hσ).2.1 d h

/-- **Naturality** of the connectors: `unit_S ; P(σ) = σ ; unit_T` on `S`. -/
theorem naturality {A B : P.Thy} {σ : Subst} (hσ : P.Hom A B σ) {c : GName}
    (h : A.S.Has c) : (unit A c).trans (mor A B σ) = (σ c).trans (unit B) :=
  (univ hσ).2.2.1 c h

theorem Hom.id (A : P.Thy) : P.Hom A A Subst.id where
  mor := IsMorphism.id _
  fixM _ _ := rfl
  lands _ h := h

theorem Hom.comp {A B C : P.Thy} {σ τ : Subst} (hσ : P.Hom A B σ) (hτ : P.Hom B C τ) :
    P.Hom A C (σ.comp τ) where
  mor := hσ.mor.comp hτ.mor
  fixM c hc := by simp [Subst.comp, hσ.fixM c hc, Term.trans, hτ.fixM c hc]
  lands c hc := (hσ.lands c hc).trans' hτ.lands

/-- Functor law: identities (on the constants of `P(S)`). -/
theorem mor_id (A : P.Thy) {d : GName} (h : (obj A).Has d) :
    mor A A Subst.id d = .const d :=
  ((univ (Hom.id A)).2.2.2 Subst.id (fun _ _ => rfl)
    (fun c _ => by rw [Term.trans_id]; rfl) d h).symm

/-- Functor law: composition (on the constants of `P(S)`). -/
theorem mor_comp {A B C : P.Thy} {σ τ : Subst} (hσ : P.Hom A B σ) (hτ : P.Hom B C τ)
    {d : GName} (h : (obj A).Has d) :
    mor A C (σ.comp τ) d = ((mor A B σ).comp (mor B C τ)) d := by
  refine ((univ (hσ.comp hτ)).2.2.2 ((mor A B σ).comp (mor B C τ)) ?_ ?_ d h).symm
  · intro d hd
    simp [Subst.comp, mor_meta hσ hd, Term.trans, mor_meta hτ hd, Subst.id]
  · intro c hc
    simp only [Subst.comp]
    rw [Term.trans_comp, naturality hσ hc, ← Term.trans_comp, ← Term.trans_comp]
    exact Term.trans_congr (hσ.lands c hc) (fun c' hc' => naturality hτ hc')

end PFData

end MMT
