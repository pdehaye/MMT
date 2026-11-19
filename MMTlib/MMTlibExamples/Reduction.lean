import MMTlib

/-!
# Examples: β-reduction and confluence

`(λx:A. λy:A. x) c d` reduces to `c` in two steps. As `c` is β-normal, Church–Rosser
shows that it is the only normal form of the term, whatever the reduction order.
-/

namespace MMT.Example

open LF

/-- A constant of the example theory. -/
def cst (n : String) : Term := .const ⟨"Ex", n⟩

/-- `λx:A. λy:A. x`. -/
def kComb (A : Term) : Term := lam A (lam (A.liftN 1 0) (.var 1))

theorem kComb_red (A c d : Term) :
    Red (.app (.app (kComb A) c) d) c := by
  -- First contract the outer redex `(λx. λy. x) c`, then `(λy. c) d`.
  refine Star.head (Step.appL d (Step.beta _ _ c)) (Star.single ?_)
  have e : Term.inst 0 c (lam (A.liftN 1 0) (.var 1)) =
      lam (Term.inst 0 c (A.liftN 1 0)) (Term.liftN 1 0 c) := by
    simp [Term.inst]
  rw [e]
  have h := Step.beta (Term.inst 0 c (A.liftN 1 0)) (Term.liftN 1 0 c) d
  rwa [Term.inst_liftN_skip (k := 0) (c := 0) (j := 0) d c (Nat.le_refl 0) (Nat.le_refl 0),
    Term.liftN_zero' 0 c] at h

theorem const_normal (c : GName) : Normal (.const c) := fun _ h => by cases h

/-- Every normal form of `K c d` is `c`. -/
example (A : Term) (n : String) (u : Term) (hu : Red (.app (.app (kComb A) (cst n)) (cst "d")) u)
    (nu : Normal u) : u = cst n :=
  Red.normal_unique hu (kComb_red A (cst n) _) nu (const_normal _)

/-- Distinct constants are not β-convertible. -/
example : ¬ Conv (cst "a") (cst "b") := fun h => by
  have := Conv.normal_eq h (const_normal _) (const_normal _)
  simp [cst] at this

/-! ### The executable conversion check, evaluated in the kernel -/

/-- `K a b` and `a` are convertible: decided by comparing normal forms. -/
example : Conv (.app (.app (kComb (cst "A")) (cst "a")) (cst "b")) (cst "a") :=
  conv?_true (fuel := 5) (by decide)

/-- `K a b` and `K b a` are not convertible. -/
example : ¬ Conv (.app (.app (kComb (cst "A")) (cst "a")) (cst "b"))
    (.app (.app (kComb (cst "A")) (cst "b")) (cst "a")) :=
  conv?_false (fuel := 5) (by decide)

/-- `λx. K x x` is in normal form only after reduction. -/
example : ¬ Normal (lam (cst "A") (.app (.app (kComb (cst "A")) (.var 0)) (.var 0))) := by
  decide

end MMT.Example
