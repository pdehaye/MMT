import MMTlib.Checking.Unknowns
import MMTlib.Checking.BetaConversion

/-!
# Higher-order pattern unification

MMT's `Solver` solves constraints `?X x₁ … xₙ ≐ t`, where an unknown is applied to
bound variables (Miller's *higher-order patterns*), by `?X := λy₁ … yₙ. t[y⃗/x⃗]`. The
solution is not syntactic: instantiating the left side gives a β-redex that reduces to
`t`. This file formalizes the solution and its soundness up to β:

* `abstr i d t` abstracts the variable `i` of `t`, and `Term.inst_abstr` shows that
  instantiating it with `x_i` gives back `t`;
* `patSol` builds the λ-abstraction, and `patSol_red` shows `(patSol t) x⃗ ⟶β* t`;
* `patternSolve` solves a pattern constraint with binder types read off the context
  (`patternSolve_sound`), and `unifyP` tries patterns before first-order unification;
* `solveCheckP` solves a list of constraints and runs the sound LF checker on the
  instance. Its soundness theorem `solveCheckP_sound` states that the constraints hold up
  to β-conversion and the instantiated judgment is derivable.

Pattern solving needs no distinctness of the variables for soundness. Distinctness is
what makes the solution most general, which is not formalized here.
-/

namespace MMT

open LF

/-! ## Abstraction of a variable -/

/-- `abstr i d t`: under `d` binders, turn the variable `i` (index `d + i`) into the
innermost bound variable `d`, shifting the others up by one. -/
def abstr (i : Nat) : Nat → Term → Term
  | d, .var k => if k < d then .var k else if k = d + i then .var d else .var (k + 1)
  | _, .const c => .const c
  | d, .app f a => .app (abstr i d f) (abstr i d a)
  | d, .bind b A t => .bind (abstr i d b) (abstr i d A) (abstr i (d + 1) t)

/-- Instantiating an abstracted variable with itself gives back the term. -/
theorem Term.inst_abstr (i : Nat) : ∀ (d : Nat) (t : Term),
    Term.inst d (.var i) (abstr i d t) = t
  | d, .var k => by
    simp only [abstr]
    by_cases h1 : k < d
    · simp [h1, Term.inst]
    · by_cases h2 : k = d + i
      · simp only [h1, ↓reduceIte]
        rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        simp only [Term.inst, Nat.lt_irrefl, ↓reduceIte, Term.liftN, Nat.not_lt_zero]
        congr 1; omega
      · have h3 : ¬ (k + 1 < d) := by omega
        have h4 : ¬ (k + 1 = d) := by omega
        simp [h1, h2, Term.inst, h3, h4]
  | _, .const _ => rfl
  | d, .app f a => by simp [abstr, Term.inst, Term.inst_abstr i d f, Term.inst_abstr i d a]
  | d, .bind b A t => by
    simp [abstr, Term.inst, Term.inst_abstr i d b, Term.inst_abstr i d A,
      Term.inst_abstr i (d + 1) t]

/-! ## Spines and pattern solutions -/

/-- The application `f a₁ … aₙ`. -/
def appSpine : Term → List Term → Term
  | f, [] => f
  | f, a :: as => appSpine (.app f a) as

theorem appSpine_trans (σ : Subst) : ∀ (f : Term) (as : List Term),
    (appSpine f as).trans σ = appSpine (f.trans σ) (as.map (·.trans σ))
  | _, [] => rfl
  | f, a :: as => by simp [appSpine, appSpine_trans σ (.app f a) as, Term.trans]

theorem Red.appSpine {f f' : Term} (h : Red f f') :
    ∀ as : List Term, Red (MMT.appSpine f as) (MMT.appSpine f' as)
  | [] => h
  | a :: as => Red.appSpine (Red.appL a h) as

/-- `patSol [(A₁, i₁), …, (Aₙ, iₙ)] t = λy₁:A₁ … λyₙ:Aₙ. t[y⃗/x⃗]`, where `x_k` is the
variable `i_k`. -/
def patSol : List (Term × Nat) → Term → Term
  | [], t => t
  | (A, i) :: ps, t => lam A (abstr i 0 (patSol ps t))

/-- The pattern solution applied to the pattern variables β-reduces to the term. -/
theorem patSol_red : ∀ (ps : List (Term × Nat)) (t : Term),
    Red (appSpine (patSol ps t) (ps.map fun p => .var p.2)) t
  | [], t => .refl t
  | (A, i) :: ps, t => by
    simp only [patSol, List.map_cons, appSpine]
    have hs : Step (.app (lam A (abstr i 0 (patSol ps t))) (.var i)) (patSol ps t) := by
      have := Step.beta A (abstr i 0 (patSol ps t)) (.var i)
      rwa [Term.inst_abstr] at this
    exact Star.trans (Red.appSpine (Star.single hs) _) (patSol_red ps t)

/-! ## Solving pattern constraints -/

/-- Recognize a pattern `?X x₁ … xₙ`: an unknown applied to variables. -/
def asPattern : Term → Option (GName × List Nat)
  | .const x => if isUnknown x then some (x, []) else none
  | .app f (.var i) => (asPattern f).map fun (x, vs) => (x, vs ++ [i])
  | _ => none

theorem asPattern_sound : ∀ {s : Term} {x : GName} {vs : List Nat},
    asPattern s = some (x, vs) → isUnknown x = true ∧ s = appSpine (.const x) (vs.map .var)
  | .const y, x, vs, h => by
    simp only [asPattern] at h
    split at h
    · rename_i hy; cases h; exact ⟨hy, rfl⟩
    · cases h
  | .app f (.var i), x, vs, h => by
    simp only [asPattern] at h
    obtain ⟨⟨y, ws⟩, hf, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨hy, rfl⟩ := asPattern_sound hf
    refine ⟨hy, ?_⟩
    clear hf h
    generalize Term.const y = g
    induction ws generalizing g with
    | nil => rfl
    | cons w ws ih => exact ih _
  | .var _, _, _, h => by cases h
  | .app _ (.const _), _, _, h => by cases h
  | .app _ (.app _ _), _, _, h => by cases h
  | .app _ (.bind _ _ _), _, _, h => by cases h
  | .bind _ _ _, _, _, h => by cases h

/-- The binder type for the pattern variable `i`: its type in `Γ`, moved to the
outside of the context. -/
def patTy (Γ : Ctx) (i : Nat) : Term := (Γ[i]?.getD (.const ⟨unknownThy, "_"⟩)).liftN (i + 1) 0

/-- Solve `?X x₁ … xₙ ≐ t` by `?X := λy⃗. t[y⃗/x⃗]`, if the solution is closed and `?X` does
not occur in `t`. -/
def patternSolve (Γ : Ctx) (x : GName) (vs : List Nat) (t : Term) : Option Subst :=
  if isUnknown x && !occurs x t && closedB 0 (patSol (vs.map fun i => (patTy Γ i, i)) t) then
    some (single x (patSol (vs.map fun i => (patTy Γ i, i)) t))
  else none

theorem patternSolve_sound {Γ : Ctx} {x : GName} {vs : List Nat} {t : Term} {θ : Subst}
    (h : patternSolve Γ x vs t = some θ) :
    Solution θ ∧ Red ((appSpine (.const x) (vs.map .var)).trans θ) (t.trans θ) := by
  unfold patternSolve at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    cases h
    refine ⟨single_solution hc.1.1 (closedB_sound hc.2), ?_⟩
    rw [appSpine_trans, trans_single_not_occurs hc.1.2]
    have hv : ∀ σ : Subst, (vs.map Term.var).map (·.trans σ) = vs.map Term.var := by
      intro σ; simp [Term.trans, Function.comp_def]
    rw [hv]
    have := patSol_red (vs.map fun i => (patTy Γ i, i)) t
    simpa [Term.trans, single, Function.comp_def] using this
  · cases h

/-- Solutions fix `λ`. -/
theorem Solution.fix_lam {θ : Subst} (h : Solution θ) : θ lamN = .const lamN :=
  h.fix lamN (by decide)

/-- Unification up to β: pattern constraints by `patternSolve`, the rest first-order. -/
def unifyP (Γ : Ctx) (n : Nat) (s t : Term) : Option Subst :=
  match asPattern s with
  | some (x, vs) => (patternSolve Γ x vs t).or (unify n s t)
  | none =>
    match asPattern t with
    | some (y, ws) => (patternSolve Γ y ws s).or (unify n s t)
    | none => unify n s t

theorem unifyP_sound {Γ : Ctx} {n : Nat} {s t : Term} {θ : Subst}
    (h : unifyP Γ n s t = some θ) : Solution θ ∧ Conv (s.trans θ) (t.trans θ) := by
  have fo : unify n s t = some θ → Solution θ ∧ Conv (s.trans θ) (t.trans θ) := fun hu => by
    obtain ⟨h1, h2⟩ := unify_sound hu
    exact ⟨h1, h2 ▸ .refl _⟩
  unfold unifyP at h
  rcases hps : asPattern s with _ | ⟨x, vs⟩
  · rw [hps] at h
    simp only at h
    rcases hpt : asPattern t with _ | ⟨y, ws⟩
    · rw [hpt] at h; exact fo h
    · rw [hpt] at h
      simp only at h
      obtain ⟨_, rfl⟩ := asPattern_sound hpt
      rcases hs : patternSolve Γ y ws s with _ | θ'
      · rw [hs, Option.none_or] at h; exact fo h
      · rw [hs] at h; cases h
        obtain ⟨h1, h2⟩ := patternSolve_sound hs
        exact ⟨h1, (Conv.of_red h2).symm⟩
  · rw [hps] at h
    simp only at h
    obtain ⟨_, rfl⟩ := asPattern_sound hps
    rcases hs : patternSolve Γ x vs t with _ | θ'
    · rw [hs, Option.none_or] at h; exact fo h
    · rw [hs] at h; cases h
      obtain ⟨h1, h2⟩ := patternSolve_sound hs
      exact ⟨h1, Conv.of_red h2⟩

/-! ## Solving, then checking -/

/-- Solve a list of constraints (each in its context) from left to right. -/
def solveAllP (n : Nat) : List (Ctx × Term × Term) → Subst → Option Subst
  | [], θ => some θ
  | (Γ, s, t) :: cs, θ => do
    let θ' ← unifyP (Γ.map (·.trans θ)) n (s.trans θ) (t.trans θ)
    solveAllP n cs (θ.comp θ')

theorem solveAllP_sound {n : Nat} : ∀ {cs : List (Ctx × Term × Term)} {θ θ' : Subst},
    Solution θ → solveAllP n cs θ = some θ' →
    Solution θ' ∧ ∃ ρ, Solution ρ ∧ θ' = θ.comp ρ ∧
      ∀ c ∈ cs, Conv (c.2.1.trans θ') (c.2.2.trans θ')
  | [], θ, θ', hθ, h => by
    cases h; exact ⟨hθ, Subst.id, Solution.id, by simp, by simp⟩
  | (Γ, s, t) :: cs, θ, θ', hθ, h => by
    simp only [solveAllP, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨θ₁, h₁, h₂⟩ := h
    obtain ⟨s₁, e₁⟩ := unifyP_sound h₁
    obtain ⟨hθ', ρ, hρ, rfl, hcs⟩ := solveAllP_sound (hθ.comp s₁) h₂
    refine ⟨hθ', θ₁.comp ρ, s₁.comp hρ, by rw [Subst.comp_assoc], ?_⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [Term.trans_comp]
      exact Conv.trans_mor hρ.closed hρ.fix_lam e₁
    · exact hcs c hc

/-- Solve the constraints up to β, then check the instantiated judgment with the sound
checker. -/
def solveCheckP (S : Sig) (n : Nat) (cs : List (Ctx × Term × Term)) (Γ : Ctx) (t A : Term) :
    Option Subst :=
  match solveAllP n cs Subst.id with
  | some θ =>
    if LF.Checker.typeCheck S (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ) then some θ else none
  | none => none

/-- **Soundness of pattern solving and checking**: the solution solves every constraint
up to β-conversion, and the instantiated judgment is derivable. -/
theorem solveCheckP_sound {S : Sig} {n : Nat} {cs : List (Ctx × Term × Term)} {Γ : Ctx}
    {t A : Term} {θ : Subst} (h : solveCheckP S n cs Γ t A = some θ) :
    Solution θ ∧ (∀ c ∈ cs, Conv (c.2.1.trans θ) (c.2.2.trans θ)) ∧
    Derivable LF.foundation S (.typing (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ)) := by
  unfold solveCheckP at h
  split at h
  · rename_i θ' hs
    split at h
    · rename_i hc
      cases h
      obtain ⟨hθ, _, _, _, hcs⟩ := solveAllP_sound Solution.id hs
      exact ⟨hθ, hcs, LF.Checker.check_sound hc⟩
    · cases h
  · cases h

end MMT
