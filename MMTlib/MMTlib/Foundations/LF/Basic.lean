import MMTlib.Core.Judgment

/-!
# LF as an MMT foundation

The logical framework LF (`mmt-lf`) is the most commonly used MMT foundation.
Its symbols live in the meta-theory `LF` (`http://cds.omdoc.org/urtheories?LF`).
We encode
* `type`, `kind` as constants,
* `Π x:A. B` as `bind Pi A B`, `λ x:A. t` as `bind lam A t`,
* application as `app`.

We then prove that the LF rules are schematic, i.e. form a `Foundation`; the
general preservation theorem therefore applies to all LF-based MMT theories.
-/

namespace MMT.LF

open Term

def thy : ThyName := "LF"

def typeN : GName := ⟨thy, "type"⟩
def kindN : GName := ⟨thy, "kind"⟩
def piN   : GName := ⟨thy, "Pi"⟩
def lamN  : GName := ⟨thy, "lambda"⟩

abbrev type : Term := .const typeN
abbrev kind : Term := .const kindN
abbrev Pi (A B : Term) : Term := .bind (.const piN) A B
abbrev lam (A t : Term) : Term := .bind (.const lamN) A t
/-- Non-dependent function type `A → B`. -/
abbrev arrow (A B : Term) : Term := Pi A (B.liftN 1 0)

open Judgment

/-- The inference rules of LF (with typed equality). -/
inductive Rule : List Judgment → Judgment → Prop where
  -- universes and variables
  | univ  (Γ) : Rule [] (typing Γ type kind)
  | var   (Γ i A) : Γ[i]? = some A → Rule [] (typing Γ (.var i) (A.liftN (i + 1) 0))
  -- dependent function types
  | piType (Γ A B) : Rule [typing Γ A type, typing (A :: Γ) B type] (typing Γ (Pi A B) type)
  | piKind (Γ A B) : Rule [typing Γ A type, typing (A :: Γ) B kind] (typing Γ (Pi A B) kind)
  | lamI  (Γ A B t) : Rule [typing Γ A type, typing (A :: Γ) t B] (typing Γ (lam A t) (Pi A B))
  | appE  (Γ A B f a) : Rule [typing Γ f (Pi A B), typing Γ a A]
      (typing Γ (.app f a) (inst 0 a B))
  -- conversion
  | conv  (Γ t A B U) : Rule [typing Γ t A, equal Γ A B U] (typing Γ t B)
  -- equality: equivalence relation
  | refl  (Γ t A) : Rule [typing Γ t A] (equal Γ t t A)
  | symm  (Γ t u A) : Rule [equal Γ t u A] (equal Γ u t A)
  | trans (Γ t u v A) : Rule [equal Γ t u A, equal Γ u v A] (equal Γ t v A)
  -- equality: congruences
  | piCong (Γ A A' B B' U) : Rule [equal Γ A A' type, equal (A :: Γ) B B' (U.liftN 1 0)]
      (equal Γ (Pi A B) (Pi A' B') U)
  | lamCong (Γ A A' B t t') : Rule [equal Γ A A' type, equal (A :: Γ) t t' B]
      (equal Γ (lam A t) (lam A' t') (Pi A B))
  | appCong (Γ A B f f' a a') : Rule [equal Γ f f' (Pi A B), equal Γ a a' A]
      (equal Γ (.app f a) (.app f' a') (inst 0 a B))
  -- computation
  | beta (Γ A B t a) : Rule [typing (A :: Γ) t B, typing Γ a A]
      (equal Γ (.app (lam A t) a) (inst 0 a t) (inst 0 a B))
  | eta  (Γ A B f) : Rule [typing Γ f (Pi A B)]
      (equal Γ f (lam A (.app (f.liftN 1 0) (.var 0))) (Pi A B))

theorem Rule.stable_trans (σ : Subst) (hσ : σ.Closed) (hfix : ∀ c, c.thy = thy → σ c = .const c)
    {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.trans σ)) (j.trans σ) := by
  have ht : σ typeN = type := hfix _ rfl
  have hk : σ kindN = kind := hfix _ rfl
  have hp : σ piN = .const piN := hfix _ rfl
  have hl : σ lamN = .const lamN := hfix _ rfl
  cases h with
  | univ Γ =>
    simpa [Judgment.trans, Term.trans, ht, hk] using Rule.univ (Γ.map (·.trans σ))
  | var Γ i A hi =>
    have := Rule.var (Γ.map (·.trans σ)) i (A.trans σ) (by simp [hi])
    simpa [Judgment.trans, Term.trans, Term.trans_liftN hσ] using this
  | piType Γ A B =>
    simpa [Judgment.trans, Term.trans, ht, hp] using
      Rule.piType (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ)
  | piKind Γ A B =>
    simpa [Judgment.trans, Term.trans, ht, hk, hp] using
      Rule.piKind (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ)
  | lamI Γ A B t =>
    simpa [Judgment.trans, Term.trans, ht, hp, hl] using
      Rule.lamI (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ)
  | appE Γ A B f a =>
    simpa [Judgment.trans, Term.trans, hp, Term.trans_inst hσ] using
      Rule.appE (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (a.trans σ)
  | conv Γ t A B U =>
    simpa [Judgment.trans] using
      Rule.conv (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ) (B.trans σ) (U.trans σ)
  | refl Γ t A =>
    simpa [Judgment.trans] using Rule.refl (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ)
  | symm Γ t u A =>
    simpa [Judgment.trans] using
      Rule.symm (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (A.trans σ)
  | trans Γ t u v A =>
    simpa [Judgment.trans] using
      Rule.trans (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (v.trans σ) (A.trans σ)
  | piCong Γ A A' B B' U =>
    simpa [Judgment.trans, Term.trans, ht, hp, Term.trans_liftN hσ] using
      Rule.piCong (Γ.map (·.trans σ)) (A.trans σ) (A'.trans σ) (B.trans σ) (B'.trans σ)
        (U.trans σ)
  | lamCong Γ A A' B t t' =>
    simpa [Judgment.trans, Term.trans, ht, hp, hl] using
      Rule.lamCong (Γ.map (·.trans σ)) (A.trans σ) (A'.trans σ) (B.trans σ) (t.trans σ)
        (t'.trans σ)
  | appCong Γ A B f f' a a' =>
    simpa [Judgment.trans, Term.trans, hp, Term.trans_inst hσ] using
      Rule.appCong (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (f'.trans σ)
        (a.trans σ) (a'.trans σ)
  | beta Γ A B t a =>
    simpa [Judgment.trans, Term.trans, hl, Term.trans_inst hσ] using
      Rule.beta (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ) (a.trans σ)
  | eta Γ A B f =>
    simpa [Judgment.trans, Term.trans, hp, hl, Term.trans_liftN hσ] using
      Rule.eta (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ)

theorem Rule.stable_extend (Δ : Ctx) {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.extend Δ)) (j.extend Δ) := by
  cases h with
  | univ Γ => exact Rule.univ _
  | var Γ i A hi =>
    have hlt : i < Γ.length := by
      rcases Nat.lt_or_ge i Γ.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hi
    exact Rule.var _ i A (by rw [List.getElem?_append_left hlt]; exact hi)
  | piType Γ A B => exact Rule.piType _ A B
  | piKind Γ A B => exact Rule.piKind _ A B
  | lamI Γ A B t => exact Rule.lamI _ A B t
  | appE Γ A B f a => exact Rule.appE _ A B f a
  | conv Γ t A B U => exact Rule.conv _ t A B U
  | refl Γ t A => exact Rule.refl _ t A
  | symm Γ t u A => exact Rule.symm _ t u A
  | trans Γ t u v A => exact Rule.trans _ t u v A
  | piCong Γ A A' B B' U => exact Rule.piCong _ A A' B B' U
  | lamCong Γ A A' B t t' => exact Rule.lamCong _ A A' B t t'
  | appCong Γ A B f f' a a' => exact Rule.appCong _ A B f f' a a'
  | beta Γ A B t a => exact Rule.beta _ A B t a
  | eta Γ A B f => exact Rule.eta _ A B f

/-- LF as an MMT foundation. -/
def foundation : Foundation where
  metaSym c := c.thy = thy
  Rule := Rule
  stable_trans σ hσ hfix _ _ h := Rule.stable_trans σ hσ hfix h
  stable_extend Δ _ _ h := Rule.stable_extend Δ h

end MMT.LF
