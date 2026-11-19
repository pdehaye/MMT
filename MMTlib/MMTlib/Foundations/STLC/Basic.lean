import MMTlib.Core.Judgment

/-!
# The simply typed λ-calculus as a foundation

A second foundation besides LF: types are terms of `tp`, function types are written as
binders that ignore their variable, and terms are built from variables, constants, λ
and application. Its rules are stable under translation and context extension, so all
generic results about foundations apply to it.
-/

namespace MMT

open Term Judgment

/-! ## The simply typed λ-calculus -/

namespace STLC

/-- The name of the meta-theory STLC. -/
def thy : ThyName := "STLC"
/-- The universe of types. -/
def tpN  : GName := ⟨thy, "tp"⟩
/-- The function-type former. -/
def arrN : GName := ⟨thy, "arrow"⟩
/-- The λ binder. -/
def lamN : GName := ⟨thy, "lambda"⟩

/-- `tp` -/
abbrev tp : Term := .const tpN
/-- `A → B`, as a binder that ignores its variable. -/
abbrev arr (A B : Term) : Term := .bind (.const arrN) A (B.liftN 1 0)
/-- `λ x:A. t` -/
abbrev lam (A t : Term) : Term := .bind (.const lamN) A t

/-- The rules of STLC. -/
inductive Rule : List Judgment → Judgment → Prop where
  /-- A variable has the (lifted) type of its context entry. -/
  | var (Γ i A) : Γ[i]? = some A → Rule [] (typing Γ (.var i) (A.liftN (i + 1) 0))
  /-- Function types of types are types. -/
  | arrF (Γ A B) : Rule [typing Γ A tp, typing Γ B tp] (typing Γ (arr A B) tp)
  /-- λ-abstraction. -/
  | lamI (Γ A B t) : Rule [typing Γ A tp, typing (A :: Γ) t (B.liftN 1 0)]
      (typing Γ (lam A t) (arr A B))
  /-- Application. -/
  | appE (Γ A B f a) : Rule [typing Γ f (arr A B), typing Γ a A] (typing Γ (.app f a) B)
  /-- Reflexivity of equality. -/
  | refl (Γ t A) : Rule [typing Γ t A] (equal Γ t t A)
  /-- Symmetry of equality. -/
  | symm (Γ t u A) : Rule [equal Γ t u A] (equal Γ u t A)
  /-- Transitivity of equality. -/
  | trans (Γ t u v A) : Rule [equal Γ t u A, equal Γ u v A] (equal Γ t v A)
  /-- Congruence for application. -/
  | appCong (Γ A B f f' a a') : Rule [equal Γ f f' (arr A B), equal Γ a a' A]
      (equal Γ (.app f a) (.app f' a') B)
  /-- Congruence for λ. -/
  | lamCong (Γ A B t t') : Rule [typing Γ A tp, equal (A :: Γ) t t' (B.liftN 1 0)]
      (equal Γ (lam A t) (lam A t') (arr A B))
  /-- β-equality. -/
  | beta (Γ A B t a) : Rule [typing (A :: Γ) t (B.liftN 1 0), typing Γ a A]
      (equal Γ (.app (lam A t) a) (inst 0 a t) B)

theorem Rule.stable_trans (σ : Subst) (hσ : σ.Closed) (hfix : ∀ c, c.thy = thy → σ c = .const c)
    {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.trans σ)) (j.trans σ) := by
  have ht : σ tpN = tp := hfix _ rfl
  have ha : σ arrN = .const arrN := hfix _ rfl
  have hl : σ lamN = .const lamN := hfix _ rfl
  cases h with
  | var Γ i A hi =>
    have := Rule.var (Γ.map (·.trans σ)) i (A.trans σ) (by simp [hi])
    simpa [Judgment.trans, Term.trans, Term.trans_liftN hσ] using this
  | arrF Γ A B =>
    simpa [Judgment.trans, Term.trans, ht, ha, Term.trans_liftN hσ] using
      Rule.arrF (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ)
  | lamI Γ A B t =>
    simpa [Judgment.trans, Term.trans, ht, ha, hl, Term.trans_liftN hσ] using
      Rule.lamI (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ)
  | appE Γ A B f a =>
    simpa [Judgment.trans, Term.trans, ha, Term.trans_liftN hσ] using
      Rule.appE (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (a.trans σ)
  | refl Γ t A => simpa [Judgment.trans] using Rule.refl (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ)
  | symm Γ t u A =>
    simpa [Judgment.trans] using Rule.symm (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (A.trans σ)
  | trans Γ t u v A =>
    simpa [Judgment.trans] using
      Rule.trans (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (v.trans σ) (A.trans σ)
  | appCong Γ A B f f' a a' =>
    simpa [Judgment.trans, Term.trans, ha, Term.trans_liftN hσ] using
      Rule.appCong (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (f'.trans σ)
        (a.trans σ) (a'.trans σ)
  | lamCong Γ A B t t' =>
    simpa [Judgment.trans, Term.trans, ht, ha, hl, Term.trans_liftN hσ] using
      Rule.lamCong (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ) (t'.trans σ)
  | beta Γ A B t a =>
    simpa [Judgment.trans, Term.trans, hl, Term.trans_liftN hσ, Term.trans_inst hσ] using
      Rule.beta (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ) (a.trans σ)

theorem Rule.stable_extend (Δ : Ctx) {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.extend Δ)) (j.extend Δ) := by
  cases h with
  | var Γ i A hi =>
    have hlt : i < Γ.length := by
      rcases Nat.lt_or_ge i Γ.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hi
    exact Rule.var _ i A (by rw [List.getElem?_append_left hlt]; exact hi)
  | arrF => exact Rule.arrF _ _ _
  | lamI => exact Rule.lamI _ _ _ _
  | appE => exact Rule.appE _ _ _ _ _
  | refl => exact Rule.refl _ _ _
  | symm => exact Rule.symm _ _ _ _
  | trans => exact Rule.trans _ _ _ _ _
  | appCong => exact Rule.appCong _ _ _ _ _ _ _
  | lamCong => exact Rule.lamCong _ _ _ _ _
  | beta => exact Rule.beta _ _ _ _ _

/-- STLC as an MMT foundation. -/
def foundation : Foundation where
  metaSym c := c.thy = thy
  Rule := Rule
  stable_trans σ hσ hfix _ _ h := Rule.stable_trans σ hσ hfix h
  stable_extend Δ _ _ h := Rule.stable_extend Δ h

end STLC

end MMT
