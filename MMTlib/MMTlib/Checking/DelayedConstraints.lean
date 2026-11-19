import MMTlib.Checking.PatternUnification

/-!
# Delayed constraints

MMT's `Solver` does not fail on a constraint it cannot solve yet: it *delays* it and
retries once other constraints have produced solutions. Here constraints are first
β-normalized and then unified (`unifyN`, patterns included), so solving one unknown
can turn another constraint into a solvable one. For example, `?F ?A ≐ c` cannot be
solved before `?F`, but once `?F := λx. x` it normalizes to `?A ≐ c`.

* `solvePass` tries every constraint once and returns the delayed ones;
* `solveDelayed` repeats passes while they make progress;
* `solveCheckD` then runs the sound LF checker on the instance.

Soundness (`solveDelayed_sound`, `solveCheckD_sound`): every constraint holds up to
β-conversion under the final solution, which extends the earlier ones. This needs
that solutions preserve conversion (`LF.Conv.trans_mor`), since a constraint solved
early must stay solved under later solutions.
-/

namespace MMT

open LF

/-- A constraint `Γ ⊢ s ≐ t`. -/
abbrev Constraint := Ctx × Term × Term

/-- `t` normalized with the given fuel, or `t` itself if the fuel runs out. -/
def normB (n : Nat) (t : Term) : Term := (nf n t).getD t

theorem red_normB (n : Nat) (t : Term) : Red t (normB n t) := by
  unfold normB
  cases h : nf n t with
  | none => exact .refl t
  | some v => exact (nf_sound h).1

/-- Unification up to β: normalize, then unify (patterns first). -/
def unifyN (Γ : Ctx) (n : Nat) (s t : Term) : Option Subst :=
  unifyP Γ n (normB n s) (normB n t)

theorem unifyN_sound {Γ : Ctx} {n : Nat} {s t : Term} {θ : Subst}
    (h : unifyN Γ n s t = some θ) : Solution θ ∧ Conv (s.trans θ) (t.trans θ) := by
  obtain ⟨hθ, hc⟩ := unifyP_sound h
  refine ⟨hθ, ?_⟩
  have hs := Conv.trans_mor hθ.closed hθ.fix_lam (Conv.of_red (red_normB n s))
  have ht := Conv.trans_mor hθ.closed hθ.fix_lam (Conv.of_red (red_normB n t))
  exact (hs.trans hc).trans ht.symm

/-- A constraint holds up to β under `θ`. -/
def Constraint.Holds (θ : Subst) (c : Constraint) : Prop := Conv (c.2.1.trans θ) (c.2.2.trans θ)

/-- Once a constraint holds, it keeps holding under further solutions. -/
theorem Constraint.Holds.comp {θ ρ : Subst} {c : Constraint} (h : c.Holds θ) (hρ : Solution ρ) :
    c.Holds (θ.comp ρ) := by
  unfold Constraint.Holds at *
  simp only [Term.trans_comp]
  exact Conv.trans_mor hρ.closed hρ.fix_lam h

/-- One pass over the constraints: solve what can be solved, delay the rest. -/
def solvePass (n : Nat) : List Constraint → Subst → Subst × List Constraint
  | [], θ => (θ, [])
  | (Γ, s, t) :: cs, θ =>
    match unifyN (Γ.map (·.trans θ)) n (s.trans θ) (t.trans θ) with
    | some θ' => solvePass n cs (θ.comp θ')
    | none =>
      let r := solvePass n cs θ
      (r.1, (Γ, s, t) :: r.2)

/-- The invariant of a pass: the result extends the input by a solution, and every
constraint holds or is delayed. -/
theorem solvePass_sound {n : Nat} : ∀ {cs : List Constraint} {θ : Subst}, Solution θ →
    Solution (solvePass n cs θ).1 ∧
    (∃ ρ, Solution ρ ∧ (solvePass n cs θ).1 = θ.comp ρ) ∧
    (solvePass n cs θ).2.length ≤ cs.length ∧
    ∀ c ∈ cs, c ∈ (solvePass n cs θ).2 ∨ c.Holds (solvePass n cs θ).1
  | [], θ, hθ => ⟨hθ, ⟨Subst.id, Solution.id, by simp [solvePass]⟩, by simp [solvePass], by simp⟩
  | (Γ, s, t) :: cs, θ, hθ => by
    unfold solvePass
    split
    · rename_i θ' hu
      obtain ⟨hθ', hc⟩ := unifyN_sound hu
      obtain ⟨h1, ⟨ρ, hρ, e⟩, h3, h4⟩ := solvePass_sound (n := n) (cs := cs) (hθ.comp hθ')
      refine ⟨h1, ⟨θ'.comp ρ, hθ'.comp hρ, by rw [e, Subst.comp_assoc]⟩, by simp; omega, ?_⟩
      intro c hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · right
        rw [e]
        have : Constraint.Holds (θ.comp θ') (Γ, s, t) := by
          unfold Constraint.Holds; simpa only [Term.trans_comp] using hc
        exact this.comp hρ
      · exact h4 c hc'
    · obtain ⟨h1, h2, h3, h4⟩ := solvePass_sound (n := n) (cs := cs) hθ
      refine ⟨h1, h2, by simp; omega, ?_⟩
      intro c hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · left; simp
      · rcases h4 c hc' with h | h
        · left; simp [h]
        · right; exact h

/-- Repeat passes while they make progress, with at most `fuel` passes. -/
def solveDelayed (n : Nat) : Nat → List Constraint → Subst → Option Subst
  | 0, _, _ => none
  | k + 1, cs, θ =>
    let r := solvePass n cs θ
    if r.2.isEmpty then some r.1
    else if r.2.length < cs.length then solveDelayed n k r.2 r.1
    else none

/-- **Soundness of solving with delays**: the result is a solution extending the input,
under which every constraint holds up to β. -/
theorem solveDelayed_sound {n : Nat} : ∀ {k : Nat} {cs : List Constraint} {θ θ' : Subst},
    Solution θ → solveDelayed n k cs θ = some θ' →
    Solution θ' ∧ (∃ ρ, Solution ρ ∧ θ' = θ.comp ρ) ∧ ∀ c ∈ cs, c.Holds θ'
  | 0, _, _, _, _, h => by cases h
  | k + 1, cs, θ, θ', hθ, h => by
    unfold solveDelayed at h
    obtain ⟨h1, ⟨ρ, hρ, e⟩, _, h4⟩ := solvePass_sound (n := n) (cs := cs) hθ
    simp only at h
    split at h
    · rename_i hemp
      cases h
      refine ⟨h1, ⟨ρ, hρ, e⟩, fun c hc => ?_⟩
      rcases h4 c hc with h | h
      · simp [List.isEmpty_iff.mp hemp] at h
      · exact h
    · split at h
      · obtain ⟨g1, ⟨σ, hσ, e'⟩, g3⟩ := solveDelayed_sound h1 h
        refine ⟨g1, ⟨ρ.comp σ, hρ.comp hσ, by rw [e', e, Subst.comp_assoc]⟩, fun c hc => ?_⟩
        rcases h4 c hc with h | h
        · exact g3 c h
        · rw [e']; exact h.comp hσ
      · cases h

/-- Solve with delays, then check the instantiated judgment with the sound checker. -/
def solveCheckD (S : Sig) (n fuel : Nat) (cs : List Constraint) (Γ : Ctx) (t A : Term) :
    Option Subst :=
  match solveDelayed n fuel cs Subst.id with
  | some θ =>
    if LF.Checker.typeCheck S (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ) then some θ else none
  | none => none

/-- **Soundness**: every constraint holds up to β and the instance is derivable. -/
theorem solveCheckD_sound {S : Sig} {n fuel : Nat} {cs : List Constraint} {Γ : Ctx}
    {t A : Term} {θ : Subst} (h : solveCheckD S n fuel cs Γ t A = some θ) :
    Solution θ ∧ (∀ c ∈ cs, c.Holds θ) ∧
    Derivable LF.foundation S (.typing (Γ.map (·.trans θ)) (t.trans θ) (A.trans θ)) := by
  unfold solveCheckD at h
  split at h
  · rename_i θ' hs
    split at h
    · rename_i hc
      cases h
      obtain ⟨hθ, _, hcs⟩ := solveDelayed_sound Solution.id hs
      exact ⟨hθ, hcs, LF.Checker.check_sound hc⟩
    · cases h
  · cases h

end MMT
