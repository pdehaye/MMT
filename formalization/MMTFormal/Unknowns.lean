import MMTFormal.Checker

/-!
# Unknowns and their solutions

MMT's `Solver` (`api/checking/Solver.scala`) checks judgments that contain *unknowns*:
placeholders for omitted arguments, declared with a type in the checking context. It
treats them as constants while checking, collects solutions, and finally instantiates
the judgment with the solution.

This file formalizes what makes that sound:
* unknowns are constants of a reserved theory `?`;
* a *solution* `θ` sends unknowns to closed terms and is the identity elsewhere;
* `solution_isMorphism`: if every solution has the declared type of its unknown, then
  `θ` is a well-typed morphism from the signature extended by the unknowns back to the
  signature. By judgment preservation, everything derived with unknowns holds for the
  instantiated judgment (`solution_transport`);
* `unify`: first-order unification of terms with unknowns, with soundness
  (`unify_sound`): the result is a solution that makes both sides syntactically equal;
* `solveCheck`: solve a list of constraints by unification, then run the sound LF checker
  on the instantiated judgment. Success implies derivability (`solveCheck_sound`).

The model covers the soundness principle and a simple solving strategy. It does not
cover MMT's delayed constraints or higher-order patterns.
-/

namespace MMT

/-- The reserved theory of unknowns. -/
def unknownThy : ThyName := "?"

/-- Is `c` an unknown? -/
def isUnknown (c : GName) : Bool := c.thy == unknownThy

/-- A solution: closed images, identity on everything but unknowns. -/
structure Solution (θ : Subst) : Prop where
  closed : θ.Closed
  fix : ∀ c, isUnknown c = false → θ c = .const c

theorem Solution.id : Solution Subst.id := ⟨Subst.Closed.id, fun _ _ => rfl⟩

theorem Solution.comp {θ θ' : Subst} (h : Solution θ) (h' : Solution θ') :
    Solution (θ.comp θ') :=
  ⟨h.closed.comp h'.closed, fun c hc => by simp [Subst.comp, h.fix c hc, Term.trans, h'.fix c hc]⟩

/-- A signature extended by declarations of unknowns. -/
def Sig.withUnknowns (S U : Sig) : Sig := fun c => if isUnknown c then U c else S c

/-- `t` contains no unknowns. -/
def NoUnknowns (t : Term) : Prop := t.UsesOnly fun c => isUnknown c = false

theorem Solution.trans_noUnknowns {θ : Subst} (h : Solution θ) {t : Term} (ht : NoUnknowns t) :
    t.trans θ = t := by
  rw [Term.trans_congr ht (τ := Subst.id) (fun c hc => h.fix c hc), Term.trans_id]

/-- **Solutions are morphisms.** If the declarations of `S` contain no unknowns and every
unknown's solution has its declared type (instantiated), then `θ : S ∪ U → S` is a
well-typed morphism. -/
theorem solution_isMorphism {S U : Sig} {θ : Subst} (hθ : Solution θ)
    (hS : ∀ c i, S c = some i → (∀ A, i.tp = some A → NoUnknowns A) ∧
      ∀ e, i.df = some e → NoUnknowns e)
    (hU : ∀ x A d, isUnknown x = true → U x = some ⟨some A, d⟩ →
      Derivable LF.foundation S (.typing [] (θ x) (A.trans θ)) ∧
      ∀ e, d = some e → Derivable LF.foundation S (.equal [] (θ x) (e.trans θ) (A.trans θ))) :
    IsMorphism LF.foundation (S.withUnknowns U) S θ where
  closed := hθ.closed
  fixMeta c hc := hθ.fix c (by
    simp only [LF.foundation] at hc
    simp [isUnknown, hc, unknownThy, LF.thy])
  typed {c A d} hc := by
    unfold Sig.withUnknowns at hc
    cases hu : isUnknown c
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hc
      rw [hθ.fix c hu, hθ.trans_noUnknowns ((hS c _ hc).1 A rfl)]
      exact .const hc
    · simp only [hu, ↓reduceIte] at hc
      exact (hU c A d hu hc).1
  defn {c A d} hc := by
    unfold Sig.withUnknowns at hc
    cases hu : isUnknown c
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hc
      rw [hθ.fix c hu, hθ.trans_noUnknowns ((hS c _ hc).1 A rfl),
        hθ.trans_noUnknowns ((hS c _ hc).2 d rfl)]
      exact .defn hc
    · simp only [hu, ↓reduceIte] at hc
      exact (hU c A (some d) hu hc).2 d rfl

/-- **Soundness of checking with unknowns**: whatever is derivable while treating the
unknowns as declared constants holds for the judgment instantiated with the solution. -/
theorem solution_transport {S U : Sig} {θ : Subst} (hθ : Solution θ)
    (hS : ∀ c i, S c = some i → (∀ A, i.tp = some A → NoUnknowns A) ∧
      ∀ e, i.df = some e → NoUnknowns e)
    (hU : ∀ x A d, isUnknown x = true → U x = some ⟨some A, d⟩ →
      Derivable LF.foundation S (.typing [] (θ x) (A.trans θ)) ∧
      ∀ e, d = some e → Derivable LF.foundation S (.equal [] (θ x) (e.trans θ) (A.trans θ)))
    {J : Judgment} (hJ : Derivable LF.foundation (S.withUnknowns U) J) :
    Derivable LF.foundation S (J.trans θ) :=
  Derivable.trans (solution_isMorphism hθ hS hU) hJ

/-! ## First-order unification -/

/-- Does the unknown `x` occur in `t`? -/
def occurs (x : GName) : Term → Bool
  | .var _ => false
  | .const c => c == x
  | .app f a => occurs x f || occurs x a
  | .bind b A t => occurs x b || occurs x A || occurs x t

/-- Is `t` closed? (Decidable version of `ClosedAt 0`.) -/
def closedB : Nat → Term → Bool
  | n, .var i => i < n
  | _, .const _ => true
  | n, .app f a => closedB n f && closedB n a
  | n, .bind b A t => closedB n b && closedB n A && closedB (n + 1) t

theorem closedB_sound : ∀ {n : Nat} {t : Term}, closedB n t = true → t.ClosedAt n
  | n, .var i, h => by show i < n; simpa [closedB] using h
  | _, .const _, _ => trivial
  | n, .app f a, h => by
    simp only [closedB, Bool.and_eq_true] at h
    exact ⟨closedB_sound h.1, closedB_sound h.2⟩
  | n, .bind b A t, h => by
    simp only [closedB, Bool.and_eq_true] at h
    exact ⟨closedB_sound h.1.1, closedB_sound h.1.2, closedB_sound h.2⟩

/-- The solution `x ↦ t`. -/
def single (x : GName) (t : Term) : Subst := fun c => if c = x then t else .const c

theorem trans_single_not_occurs {x : GName} {t : Term} : ∀ {s : Term}, occurs x s = false →
    s.trans (single x t) = s
  | .var _, _ => rfl
  | .const c, h => by
    simp only [occurs, beq_eq_false_iff_ne, ne_eq] at h
    simp [Term.trans, single, h]
  | .app f a, h => by
    simp only [occurs, Bool.or_eq_false_iff] at h
    simp [Term.trans, trans_single_not_occurs h.1, trans_single_not_occurs h.2]
  | .bind b A s, h => by
    simp only [occurs, Bool.or_eq_false_iff] at h
    simp [Term.trans, trans_single_not_occurs h.1.1, trans_single_not_occurs h.1.2,
      trans_single_not_occurs h.2]

theorem single_solution {x : GName} {t : Term} (hx : isUnknown x = true) (ht : t.ClosedAt 0) :
    Solution (single x t) where
  closed c := by unfold single; split <;> trivial
  fix c hc := by
    have : c ≠ x := by rintro rfl; rw [hx] at hc; cases hc
    simp [single, this]

/-- Solve `x := t`, if `x` is an unknown not occurring in the closed term `t`. -/
def bindVar (x : GName) (t : Term) : Option Subst :=
  if isUnknown x && !occurs x t && closedB 0 t then some (single x t) else none

/-- Solve a constraint `x = t`, or `t = x` if `t` is itself an unknown. -/
def unifyConst (x : GName) (t : Term) : Option Subst :=
  (bindVar x t).or (match t with
    | .const y => bindVar y (.const x)
    | _ => none)

/-- First-order unification of terms with unknowns. -/
def unify : Nat → Term → Term → Option Subst
  | 0, _, _ => none
  | n + 1, s, t =>
    if s = t then some Subst.id else
    match s, t with
    | .const x, t => unifyConst x t
    | s, .const y => bindVar y s
    | .app f a, .app g b => do
      let θ₁ ← unify n f g
      let θ₂ ← unify n (a.trans θ₁) (b.trans θ₁)
      pure (θ₁.comp θ₂)
    | .bind c A u, .bind d B v => do
      let θ₁ ← unify n c d
      let θ₂ ← unify n (A.trans θ₁) (B.trans θ₁)
      let θ₃ ← unify n ((u.trans θ₁).trans θ₂) ((v.trans θ₁).trans θ₂)
      pure ((θ₁.comp θ₂).comp θ₃)
    | _, _ => none

theorem bindVar_sound {x : GName} {t : Term} {θ : Subst} (h : bindVar x t = some θ) :
    Solution θ ∧ (Term.const x).trans θ = t.trans θ := by
  unfold bindVar at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    cases h
    refine ⟨single_solution hc.1.1 (closedB_sound hc.2), ?_⟩
    simp [Term.trans, single, trans_single_not_occurs hc.1.2]
  · cases h

theorem unifyConst_sound {x : GName} {t : Term} {θ : Subst} (h : unifyConst x t = some θ) :
    Solution θ ∧ (Term.const x).trans θ = t.trans θ := by
  unfold unifyConst at h
  rcases hb : bindVar x t with _ | θ'
  · rw [hb] at h
    simp only [Option.none_or] at h
    cases t with
    | const y => obtain ⟨h1, h2⟩ := bindVar_sound h; exact ⟨h1, h2.symm⟩
    | var => cases h
    | app => cases h
    | bind => cases h
  · rw [hb] at h; cases h; exact bindVar_sound hb

/-- **Soundness of unification**: a unifier is a solution, and it makes both sides equal. -/
theorem unify_sound : ∀ {n : Nat} {s t : Term} {θ : Subst}, unify n s t = some θ →
    Solution θ ∧ s.trans θ = t.trans θ
  | 0, _, _, _, h => by simp [unify] at h
  | n + 1, s, t, θ, h => by
    by_cases hst : s = t
    · simp only [unify, hst, ↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨Solution.id, by rw [hst]⟩
    · simp only [unify, hst, ↓reduceIte] at h
      cases s with
      | const x => exact unifyConst_sound h
      | var i =>
        cases t with
        | const y => obtain ⟨h1, h2⟩ := bindVar_sound h; exact ⟨h1, h2.symm⟩
        | _ => cases h
      | app f a =>
        cases t with
        | const y => obtain ⟨h1, h2⟩ := bindVar_sound h; exact ⟨h1, h2.symm⟩
        | app g b =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨θ₁, h₁, θ₂, h₂, rfl⟩ := h
          obtain ⟨s₁, e₁⟩ := unify_sound h₁
          obtain ⟨s₂, e₂⟩ := unify_sound h₂
          refine ⟨s₁.comp s₂, ?_⟩
          simp [Term.trans, Term.trans_comp, e₁, e₂]
        | _ => cases h
      | bind c A u =>
        cases t with
        | const y => obtain ⟨h1, h2⟩ := bindVar_sound h; exact ⟨h1, h2.symm⟩
        | bind d B v =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨θ₁, h₁, θ₂, h₂, θ₃, h₃, rfl⟩ := h
          obtain ⟨s₁, e₁⟩ := unify_sound h₁
          obtain ⟨s₂, e₂⟩ := unify_sound h₂
          obtain ⟨s₃, e₃⟩ := unify_sound h₃
          refine ⟨(s₁.comp s₂).comp s₃, ?_⟩
          simp [Term.trans, Term.trans_comp, e₁, e₂, e₃]
        | _ => cases h

/-! ## Solving constraints, then checking -/

/-- Solve a list of equality constraints from left to right. -/
def solveAll (n : Nat) : List (Term × Term) → Subst → Option Subst
  | [], θ => some θ
  | (s, t) :: cs, θ => do
    let θ' ← unify n (s.trans θ) (t.trans θ)
    solveAll n cs (θ.comp θ')

theorem solveAll_sound {n : Nat} : ∀ {cs : List (Term × Term)} {θ θ' : Subst},
    Solution θ → solveAll n cs θ = some θ' →
    Solution θ' ∧ ∃ ρ, Solution ρ ∧ θ' = θ.comp ρ ∧ ∀ c ∈ cs, c.1.trans θ' = c.2.trans θ'
  | [], θ, θ', hθ, h => by
    cases h; exact ⟨hθ, Subst.id, Solution.id, by simp, by simp⟩
  | (s, t) :: cs, θ, θ', hθ, h => by
    simp only [solveAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨θ₁, h₁, h₂⟩ := h
    obtain ⟨s₁, e₁⟩ := unify_sound h₁
    obtain ⟨hθ', ρ, hρ, rfl, hcs⟩ := solveAll_sound (hθ.comp s₁) h₂
    refine ⟨hθ', θ₁.comp ρ, s₁.comp hρ, by rw [Subst.comp_assoc], ?_⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [Term.trans_comp]; rw [e₁]
    · exact hcs c hc

/-- Solve the constraints, then check the instantiated judgment with the sound checker. -/
def solveCheck (S : Sig) (n : Nat) (cs : List (Term × Term)) (Γ : Ctx) (t A : Term) :
    Option Subst :=
  match solveAll n cs Subst.id with
  | some θ =>
    if LF.Checker.typeCheck S (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ) then some θ else none
  | none => none

/-- **Soundness of solving and checking**: the solution solves every constraint, and the
instantiated judgment is derivable. -/
theorem solveCheck_sound {S : Sig} {n : Nat} {cs : List (Term × Term)} {Γ : Ctx} {t A : Term}
    {θ : Subst} (h : solveCheck S n cs Γ t A = some θ) :
    Solution θ ∧ (∀ c ∈ cs, c.1.trans θ = c.2.trans θ) ∧
    Derivable LF.foundation S (.typing (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ)) := by
  unfold solveCheck at h
  split at h
  · rename_i θ' hs
    split at h
    · rename_i hc
      cases h
      obtain ⟨hθ, _, _, _, hcs⟩ := solveAll_sound Solution.id hs
      exact ⟨hθ, hcs, LF.Checker.check_sound hc⟩
    · cases h
  · cases h

/-! ## Solved unknowns as definitions

Once an unknown is solved, MMT's `Solver` records the solution as its definiens, so that
further checking unfolds it by δ-conversion. Here a list of solved unknowns
`?x : A := t` is turned into declarations, the judgment is checked with them, and each
solution is checked against its (instantiated) type. -/

/-- A solved unknown `?name : tp := sol`. -/
structure Solved where
  name : LName
  tp : Term
  sol : Term

/-- Look up a solved unknown. -/
def findSolved (us : List Solved) (c : GName) : Option Solved :=
  if isUnknown c then us.find? (fun u => u.name == c.name) else none

/-- The declarations of the solved unknowns. -/
def solvedSig (us : List Solved) : Sig := fun c =>
  (findSolved us c).map fun u => ⟨some u.tp, some u.sol⟩

/-- The solution of the solved unknowns. -/
def solvedSubst (us : List Solved) : Subst := fun c =>
  match findSolved us c with
  | some u => u.sol
  | none => .const c

/-- Decidable version of `NoUnknowns`. -/
def noUnkB : Term → Bool
  | .var _ => true
  | .const c => !isUnknown c
  | .app f a => noUnkB f && noUnkB a
  | .bind b A t => noUnkB b && noUnkB A && noUnkB t

theorem noUnkB_sound : ∀ {t : Term}, noUnkB t = true → NoUnknowns t
  | .var _, _ => trivial
  | .const c, h => by simpa [noUnkB, NoUnknowns, Term.UsesOnly] using h
  | .app f a, h => by
    simp only [noUnkB, Bool.and_eq_true] at h
    exact ⟨noUnkB_sound h.1, noUnkB_sound h.2⟩
  | .bind b A t, h => by
    simp only [noUnkB, Bool.and_eq_true] at h
    exact ⟨noUnkB_sound h.1.1, noUnkB_sound h.1.2, noUnkB_sound h.2⟩

/-- Check a judgment in the presence of solved unknowns, and check the solutions. -/
def checkSolved (S : Sig) (us : List Solved) (Γ : Ctx) (t A : Term) : Bool :=
  LF.Checker.typeCheck (S.withUnknowns (solvedSig us)) Γ t A &&
  us.all fun u => closedB 0 u.sol && noUnkB u.sol &&
    LF.Checker.typeCheck S [] u.sol (u.tp.trans (solvedSubst us))

theorem findSolved_mem {us : List Solved} {c : GName} {u : Solved}
    (h : findSolved us c = some u) : u ∈ us ∧ isUnknown c = true := by
  unfold findSolved at h
  split at h
  · exact ⟨List.mem_of_find?_eq_some h, by assumption⟩
  · cases h

/-- **Soundness of checking with solved unknowns**: the judgment instantiated with the
solutions is derivable without unknowns. -/
theorem checkSolved_sound {S : Sig} {us : List Solved} {Γ : Ctx} {t A : Term}
    (hS : ∀ c i, S c = some i → (∀ A, i.tp = some A → NoUnknowns A) ∧
      ∀ e, i.df = some e → NoUnknowns e)
    (h : checkSolved S us Γ t A = true) :
    Derivable LF.foundation S (.typing (Γ.map (·.trans (solvedSubst us)))
      (t.trans (solvedSubst us)) (A.trans (solvedSubst us))) := by
  simp only [checkSolved, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hJ, hus⟩ := h
  have hsol : Solution (solvedSubst us) := by
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · unfold solvedSubst
      split
      · rename_i u hu
        exact closedB_sound (hus u (findSolved_mem hu).1).1.1
      · trivial
    · unfold solvedSubst findSolved
      simp [hc]
  have := solution_transport (U := solvedSig us) hsol hS (fun x A' d hx hU => by
    simp only [solvedSig, Option.map_eq_some_iff] at hU
    obtain ⟨u, hu, hi⟩ := hU
    simp only [ConstInfo.mk.injEq, Option.some.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨⟨_, hnu⟩, hty⟩ := hus u (findSolved_mem hu).1
    have hθx : solvedSubst us x = u.sol := by simp [solvedSubst, hu]
    have htyped := LF.Checker.check_sound hty
    refine ⟨by rw [hθx]; exact htyped, fun e he => ?_⟩
    cases he
    rw [hθx, hsol.trans_noUnknowns (noUnkB_sound hnu)]
    exact .rule (LF.Rule.refl _ _ _) (by simpa using htyped))
    (LF.Checker.check_sound hJ)
  simpa [Judgment.trans] using this

end MMT
