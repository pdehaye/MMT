import MMTlib

/-!
# Delayed constraints

The constraint `?F ?A ≐ c` can be solved only after `?F`. It is delayed in the first
pass, in which `?F ≐ λx:N. x` is solved; in the second pass it normalizes to `?A ≐ c`.
The instance `(λx:N. x) c : N` is then checked.
-/

namespace MMT.Example.Delayed

open LF

def gN : GName := ⟨"D", "N"⟩
def gC : GName := ⟨"D", "c"⟩
def gF : GName := ⟨unknownThy, "F"⟩
def gA : GName := ⟨unknownThy, "A"⟩

/-- `N : type`, `c : N`. -/
def sig : Sig := fun x =>
  if x = gN then some ⟨some LF.type, none⟩
  else if x = gC then some ⟨some (.const gN), none⟩
  else none

/-- `?F ?A ≐ c` (only solvable later) and `?F ≐ λx:N. x`. -/
def constraints : List Constraint :=
  [([], .app (.const gF) (.const gA), .const gC), ([], .const gF, lam (.const gN) (.var 0))]

/-- Without delays, the first constraint fails. -/
theorem undelayed_fails : solveAllP 16 constraints Subst.id = none := by decide

/-- The first pass solves only the second constraint and delays the first. -/
theorem first_pass_delays : (solvePass 16 constraints Subst.id).2 = [constraints.head!] := by
  decide

/-- With delays, all constraints are solved and `?F ?A : N` is checked. -/
theorem solved_with_delays :
    (solveCheckD sig 16 3 constraints [] (.app (.const gF) (.const gA)) (.const gN)).isSome
      = true := by
  decide

/-- The judgment obtained: `?F ?A : N` holds after instantiation, and both constraints
hold up to β. -/
example : ∃ θ : Subst, Solution θ ∧ (∀ c ∈ constraints, c.Holds θ) ∧
    Derivable LF.foundation sig (.typing [] (.app (θ gF) (θ gA)) (.const gN)) := by
  obtain ⟨θ, hθ⟩ := Option.isSome_iff_exists.mp solved_with_delays
  obtain ⟨hsol, hcs, hd⟩ := solveCheckD_sound hθ
  refine ⟨θ, hsol, hcs, ?_⟩
  simpa [Term.trans, hsol.fix gN (by decide)] using hd

end MMT.Example.Delayed
