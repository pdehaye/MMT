import MMTlib

/-!
# Higher-order pattern unification

In the context `x : N`, the constraint `?F x ≐ succ x` is a higher-order pattern. It is
solved by `?F := λx:N. succ x`, which the sound checker then checks against `N → N`.
The constraint holds only up to β: `(λx:N. succ x) x ⟶β succ x`.
-/

namespace MMT.Example

open LF

def gN : GName := ⟨"Nat", "N"⟩
def gSucc : GName := ⟨"Nat", "succ"⟩
def gF : GName := ⟨unknownThy, "F"⟩

/-- `N : type`, `succ : N → N`. -/
def natSig : Sig := fun x =>
  if x = gN then some ⟨some LF.type, none⟩
  else if x = gSucc then some ⟨some (LF.arrow (.const gN) (.const gN)), none⟩
  else none

/-- The constraint `x : N ⊢ ?F x ≐ succ x`. -/
def patConstraint : Ctx × Term × Term :=
  ([.const gN], .app (.const gF) (.var 0), .app (.const gSucc) (.var 0))

theorem solve_pattern :
    (solveCheckP natSig 16 [patConstraint] [] (.const gF)
      (LF.arrow (.const gN) (.const gN))).isSome = true := by
  decide

/-- The solution is checked: `λx:N. succ x : N → N` is derivable, and it solves the
constraint up to β. -/
example : ∃ θ : Subst, Solution θ ∧
    Conv (Term.trans θ (.app (.const gF) (.var 0))) (.app (.const gSucc) (.var 0)) ∧
    Derivable LF.foundation natSig
      (.typing [] (θ gF) (LF.arrow (.const gN) (.const gN))) := by
  obtain ⟨θ, hθ⟩ := Option.isSome_iff_exists.mp solve_pattern
  obtain ⟨hsol, hcs, hd⟩ := solveCheckP_sound hθ
  refine ⟨θ, hsol, ?_, ?_⟩
  · have := hcs _ (List.mem_singleton_self _)
    simpa [patConstraint, Term.trans, hsol.fix gSucc (by decide)] using this
  · have hN : θ gN = .const gN := hsol.fix gN (by decide)
    have hP : θ piN = .const piN := hsol.fix piN (by decide)
    simpa [Term.trans, LF.arrow, hN, hP, Term.liftN] using hd

end MMT.Example
