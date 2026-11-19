import MMTlibExamples.Algebra
import MMTlib.Checking.TypeChecker

/-!
# Running the type checker

Kernel-evaluated runs of the sound LF type checker: acceptance via conversion with a
definition and via β-equality, and rejection of an ill-typed term.
-/

namespace MMT.Example

open LF

/-! ### Running the certified checker

A computable signature for `Magma`, extended by a definition `V : type = U`, so that
checking needs the conversion rule and δ-expansion. -/

def gV : GName := ⟨"Magma", "V"⟩
def V : Term := .const gV

def magmaSig : Sig := fun c =>
  if c = gU then some ⟨some type, none⟩
  else if c = gOp then some ⟨some (arrow U (arrow U U)), none⟩
  else if c = gV then some ⟨some type, some U⟩
  else none

/-- The checker accepts `x : U ⊢ op x x : U`. -/
theorem check_op_xx :
    Checker.typeCheck magmaSig [U] (.app (.app (.const gOp) (.var 0)) (.var 0)) U = true := by
  decide

/-- The checker accepts `x : U ⊢ x : V`, by conversion with `V ≡ U`. -/
theorem check_conv : Checker.typeCheck magmaSig [U] (.var 0) V = true := by
  decide

/-- The checker accepts `(λ y:U. op y y) x ≡ op x x`, by β-reduction. -/
theorem check_beta :
    Checker.eqCheck magmaSig [U]
      (.app (lam U (.app (.app (.const gOp) (.var 0)) (.var 0))) (.var 0))
      (.app (.app (.const gOp) (.var 0)) (.var 0)) U = true := by
  decide

/-- The checker rejects `x : U ⊢ op x : U`. -/
theorem reject_op_x : Checker.typeCheck magmaSig [U] (.app (.const gOp) (.var 0)) U = false := by
  decide

/-- By soundness, the accepted judgments are derivable. -/
example : Derivable LF.foundation magmaSig (.typing [U] (.var 0) V) :=
  Checker.check_sound check_conv

end MMT.Example
