import MMTFormal.Checker

/-!
# Completeness of the checker for syntax-directed typing

The checker of `Checker.lean` is sound. Here we show it is also *complete* for the
syntax-directed fragment of LF typing (`Alg`): derivations built from the variable,
constant, universe, Π, λ and application rules, where an argument's type must match the
expected one exactly (no conversion). For every such derivation the checker, given
enough fuel, infers exactly the derived type (`infer_complete`) and accepts the term
(`check_complete`).

Conversion and the equality rules are not covered. Completeness for full LF typing
would need normalization and confluence of β-reduction.
-/

namespace MMT.LF.Checker

open Term

/-- Syntax-directed LF typing. -/
inductive Alg (S : Sig) : Ctx → Term → Term → Prop where
  | var {Γ i A} : Γ[i]? = some A → Alg S Γ (.var i) (A.liftN (i + 1) 0)
  | univ {Γ} : Alg S Γ type kind
  | const {Γ c A d} : c ≠ typeN → S c = some ⟨some A, d⟩ → Alg S Γ (.const c) A
  | pi {Γ A B U} : Alg S Γ A type → Alg S (A :: Γ) B U → (U = type ∨ U = kind) →
      Alg S Γ (Pi A B) U
  | lam {Γ A B t} : Alg S Γ A type → Alg S (A :: Γ) t B → Alg S Γ (lam A t) (Pi A B)
  | app {Γ A B f a} : Alg S Γ f (Pi A B) → Alg S Γ a A → Alg S Γ (.app f a) (inst 0 a B)

/-- `check` succeeds when `infer` returns exactly the expected type. -/
theorem check_of_infer {S : Sig} {n : Nat} {Γ : Ctx} {t A : Term}
    (h : (infer S n Γ t).map (·.1) = some A) : (check S (n + 1) Γ t A).isSome = true := by
  cases hi : infer S n Γ t with
  | none => simp [hi] at h
  | some p =>
    obtain ⟨T, hT⟩ := p
    simp [hi] at h; subst h
    simp [check, hi]

/-- Inference results are stable under more fuel, once reached. -/
def Reaches (S : Sig) (Γ : Ctx) (t A : Term) : Prop :=
  ∃ n, ∀ m, n ≤ m → (infer S m Γ t).map (·.1) = some A

theorem check_reaches {S : Sig} {Γ : Ctx} {t A : Term} (h : Reaches S Γ t A) :
    ∃ n, ∀ m, n ≤ m → (check S m Γ t A).isSome = true := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, fun m hm => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact check_of_infer (hn m' (by omega))

/-- **Completeness of inference** for syntax-directed typing. -/
theorem infer_complete {S : Sig} {Γ : Ctx} {t A : Term} (h : Alg S Γ t A) : Reaches S Γ t A := by
  induction h with
  | @var Γ i A hi =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [infer]
    split
    · rename_i A' h'; rw [hi] at h'; cases h'; rfl
    · rename_i h'; rw [hi] at h'; cases h'
  | univ =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp [infer]
  | @const Γ c A d hc hS =>
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [infer, hc, dite_false]
    split
    · rename_i A' d' h'; rw [hS] at h'; cases h'; rfl
    · next hne => simp_all
  | @pi Γ A B U _ _ hU ihA ihB =>
    obtain ⟨nA, hA⟩ := check_reaches ihA
    obtain ⟨nB, hB⟩ := ihB
    refine ⟨max nA nB + 1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hcA := hA m' (by omega)
    have hiB := hB m' (by omega)
    simp only [infer, dite_true]
    cases hc : check S m' Γ A type with
    | none => rw [hc] at hcA; cases hcA
    | some pA =>
      cases hi : infer S m' (A :: Γ) B with
      | none => rw [hi] at hiB; cases hiB
      | some pB =>
        obtain ⟨U', hU'⟩ := pB
        rw [hi] at hiB; simp at hiB; subst hiB
        rcases hU with rfl | rfl
        · simp
        · simp [show kind ≠ type by decide]
  | @lam Γ A B t _ _ ihA iht =>
    obtain ⟨nA, hA⟩ := check_reaches ihA
    obtain ⟨nt, ht⟩ := iht
    refine ⟨max nA nt + 1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hcA := hA m' (by omega)
    have hit := ht m' (by omega)
    have hne : lamN ≠ piN := by decide
    simp only [infer, hne, dite_false, dite_true]
    cases hc : check S m' Γ A type with
    | none => rw [hc] at hcA; cases hcA
    | some pA =>
      cases hi : infer S m' (A :: Γ) t with
      | none => rw [hi] at hit; cases hit
      | some pB =>
        obtain ⟨B', hB'⟩ := pB
        rw [hi] at hit; simp at hit; subst hit
        rfl
  | @app Γ A B f a _ _ ihf iha =>
    obtain ⟨nf, hf⟩ := ihf
    obtain ⟨na, ha⟩ := check_reaches iha
    refine ⟨max nf na + 1, fun m hm => ?_⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hif := hf m' (by omega)
    have hca := ha m' (by omega)
    simp only [infer]
    cases hi : infer S m' Γ f with
    | none => rw [hi] at hif; cases hif
    | some pf =>
      obtain ⟨T, hT⟩ := pf
      rw [hi] at hif; simp at hif; subst hif
      simp only [dite_true]
      cases hc : check S m' Γ a A with
      | none => rw [hc] at hca; cases hca
      | some pa => rfl

/-- **Completeness of checking** for syntax-directed typing: with enough fuel, the
checker accepts every syntax-directed typing. -/
theorem check_complete {S : Sig} {Γ : Ctx} {t A : Term} (h : Alg S Γ t A) :
    ∃ n, ∀ m, n ≤ m → (check S m Γ t A).isSome = true :=
  check_reaches (infer_complete h)

/-- Every syntax-directed typing is derivable: run the (sound) checker with enough fuel. -/
theorem Alg.derivable {S : Sig} {Γ : Ctx} {t A : Term} (h : Alg S Γ t A) :
    Derivable foundation S (.typing Γ t A) := by
  obtain ⟨n, hn⟩ := check_complete h
  obtain ⟨p, _⟩ := Option.isSome_iff_exists.mp (hn n (Nat.le_refl n))
  exact p.down

end MMT.LF.Checker
