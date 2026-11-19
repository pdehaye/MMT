import MMTlib.Core.Term

/-!
# Homomorphic translation along morphisms

In MMT, every theory morphism (view, structure, include, composition) acts on terms
by *homomorphic extension* of its action on constants: each constant `c` of the
domain is replaced by a closed term `σ(c)` over the codomain, and variables, applications
and binders are kept (`Library.ApplyMorphs`, `Translator`).

We model the action on constants as a *substitution* `σ : GName → Term` and prove
the algebraic laws making translation functorial.
-/

namespace MMT

/-- The action of a morphism on constants. -/
abbrev Subst := GName → Term

namespace Term

/-- Homomorphic extension of `σ` to terms (MMT's `ApplyMorphs`). -/
def trans (σ : Subst) : Term → Term
  | var i      => var i
  | const c    => σ c
  | app f a    => app (trans σ f) (trans σ a)
  | bind b A t => bind (trans σ b) (trans σ A) (trans σ t)

end Term

namespace Subst

/-- The identity morphism. -/
def id : Subst := Term.const

/-- Diagram-order composition: first `σ`, then `τ`. -/
def comp (σ τ : Subst) : Subst := fun c => (σ c).trans τ

/-- MMT requires assignments of morphisms to be closed terms. -/
def Closed (σ : Subst) : Prop := ∀ c, (σ c).ClosedAt 0

end Subst

open Term

/-! ## Functoriality -/

@[simp] theorem Term.trans_id (t : Term) : t.trans Subst.id = t := by
  induction t <;> simp_all [trans, Subst.id]

theorem Term.trans_comp (σ τ : Subst) (t : Term) :
    t.trans (σ.comp τ) = (t.trans σ).trans τ := by
  induction t <;> simp_all [trans, Subst.comp]

@[simp] theorem Subst.id_comp (σ : Subst) : Subst.id.comp σ = σ := by
  funext c; rfl

@[simp] theorem Subst.comp_id (σ : Subst) : σ.comp Subst.id = σ := by
  funext c; simp [Subst.comp]

theorem Subst.comp_assoc (σ τ ρ : Subst) : (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext c; simp [Subst.comp, Term.trans_comp]

/-! ## Interaction with variables -/

/-- Translation preserves the free-variable bound, provided images are closed. -/
theorem Term.ClosedAt.trans {σ : Subst} (hσ : σ.Closed) {n : Nat} {t : Term}
    (h : t.ClosedAt n) : (t.trans σ).ClosedAt n := by
  induction t generalizing n with
  | var i => exact h
  | const c => exact (hσ c).mono (Nat.zero_le _)
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | bind b A t ihb ihA iht => exact ⟨ihb h.1, ihA h.2.1, iht h.2.2⟩

theorem Subst.Closed.id : Subst.id.Closed := fun _ => trivial

theorem Subst.Closed.comp {σ τ : Subst} (hσ : σ.Closed) (hτ : τ.Closed) : (σ.comp τ).Closed :=
  fun c => (hσ c).trans hτ

/-- Translation commutes with shifting. -/
theorem Term.trans_liftN {σ : Subst} (hσ : σ.Closed) (k c : Nat) (t : Term) :
    (t.liftN k c).trans σ = (t.trans σ).liftN k c := by
  induction t generalizing c with
  | var i => by_cases h : i < c <;> simp [liftN, trans, h]
  | const n => simp [liftN, trans, liftN_closed (hσ n)]
  | app f a ihf iha => simp [liftN, trans, ihf, iha]
  | bind b A t ihb ihA iht => simp [liftN, trans, ihb, ihA, iht]

/-- Translation commutes with substitution: `σ(t[u/x]) = σ(t)[σ(u)/x]`.
This is the key lemma making morphisms compatible with any foundation whose rules
are stated schematically (e.g. β-reduction). -/
theorem Term.trans_inst {σ : Subst} (hσ : σ.Closed) (j : Nat) (u t : Term) :
    (inst j u t).trans σ = inst j (u.trans σ) (t.trans σ) := by
  induction t generalizing j with
  | var i =>
    simp only [inst, trans]
    split
    · rfl
    · split
      · exact trans_liftN hσ _ _ _
      · rfl
  | const n => simp [inst, trans, inst_closed (hσ n)]
  | app f a ihf iha => simp [inst, trans, ihf, iha]
  | bind b A t ihb ihA iht => simp [inst, trans, ihb, ihA, iht]

/-! ## Constants occurring in terms -/

/-- `t.UsesOnly P`: every constant in `t` satisfies `P`. -/
def Term.UsesOnly (P : GName → Prop) : Term → Prop
  | .var _      => True
  | .const c    => P c
  | .app f a    => f.UsesOnly P ∧ a.UsesOnly P
  | .bind b A t => b.UsesOnly P ∧ A.UsesOnly P ∧ t.UsesOnly P

/-- Translation depends only on the constants that occur. -/
theorem Term.trans_congr {P : GName → Prop} {σ τ : Subst} {t : Term}
    (ht : t.UsesOnly P) (h : ∀ c, P c → σ c = τ c) : t.trans σ = t.trans τ := by
  induction t with
  | var => rfl
  | const c => exact h c ht
  | app f a ihf iha => simp [Term.trans, ihf ht.1, iha ht.2]
  | bind b A t ihb ihA iht => simp [Term.trans, ihb ht.1, ihA ht.2.1, iht ht.2.2]

end MMT
