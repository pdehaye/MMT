import MMTlibExamples.Algebra
import MMTlib.Checking.ModuleChecker

/-!
# Checking theories and views

Kernel-evaluated runs of the verified theory and view checkers, including structures in
theories and on both sides of views, and the rejection of ill-formed inputs.
-/

namespace MMT.Example

open LF

/-! ### Checking the view automatically -/

/-- The view checker accepts `plusView`. -/
theorem plusView_checks : checkView lib 4 plusView = true := by decide

/-- Hence `plusView` is well-typed, without the hand proof above. -/
theorem plusView_wellTyped' : plusView.WellTyped LF.foundation lib :=
  checkView_sound plusView_checks

def badView : View :=
  { dom := "Magma", cod := "NatArith", assign := [("U", N), ("op", .const gZero)] }

/-- A wrong view is rejected: `op ↦ zero` does not have type `N → N → N`. -/
theorem badView_rejected : checkView lib 4 badView = false := by decide

/-! ### Checking theories -/

/-- `Magma` and `NatArith` are well-formed, checked declaration by declaration. -/
theorem magma_checks : checkTheory lib 4 "Magma" = true := by decide
theorem natArith_checks : checkTheory lib 4 "NatArith" = true := by decide

theorem magma_wf : TheoryWF lib "Magma" := checkTheory_sound magma_checks

/-- A theory that uses `op` before declaring it is rejected. -/
def badThy : Theory :=
  { metaThy := some "LF",
    decls := [.const "U" (some type) none,
              .const "e" (some (.app (.const ⟨"Bad", "op"⟩) (.const ⟨"Bad", "U"⟩))) none,
              .const "op" (some (arrow (.const ⟨"Bad", "U"⟩) (.const ⟨"Bad", "U"⟩))) none] }

def badLib : Library := fun
  | "LF" => some lfThy
  | "Bad" => some badThy
  | _ => none

theorem bad_rejected : checkTheory badLib 4 "Bad" = false := by decide

/-! ### Checking with structure copies -/

/-- A view into a theory with structures: `Magma → Bimagma`, `U ↦ add/U`, `op ↦ add/op`. -/
def addView : View :=
  { dom := "Magma", cod := "Bimagma", assign := [("U", addU), ("op", .const addOp)] }

theorem addView_checks : checkView lib 4 addView = true := by decide

theorem addView_wellTyped : addView.WellTyped LF.foundation lib := checkView_sound addView_checks

/-- `Bimagma` with an extra declaration using the copies: `sq : add/U → add/U := λx. add/op x x`. -/
def bimagmaExt : Theory :=
  { metaThy := some "LF",
    decls := [.struct "add" "Magma" [],
              .const "sq" (some (arrow addU addU))
                (some (lam addU (.app (.app (.const addOp) (.var 0)) (.var 0))))] }

def libExt : Library := fun
  | "Bimagma" => some bimagmaExt
  | T => lib T

theorem bimagmaExt_checks : checkTheory libExt 4 "Bimagma" = true := by decide

/-- `Bimagma`, including its two structure declarations, is well-formed. -/
theorem bimagma_checks : checkTheory lib 4 "Bimagma" = true := by decide

/-- A structure with an assignment: `structure m : Magma = {U := N}` in a theory with `N : type`. -/
def nN : Term := .const ⟨"MagmaN", "N"⟩

def magmaN : Theory :=
  { metaThy := some "LF",
    decls := [.const "N" (some type) none, .struct "m" "Magma" [(gU, nN)]] }

/-- The same structure, but assigning `op := N`, which is ill-typed. -/
def magmaBad : Theory :=
  { metaThy := some "LF",
    decls := [.const "N" (some type) none, .struct "m" "Magma" [(gOp, nN)]] }

def libN (th : Theory) : Library := fun
  | "MagmaN" => some th
  | T => lib T

theorem magmaN_checks : checkTheory (libN magmaN) 4 "MagmaN" = true := by decide

theorem magmaBad_rejected : checkTheory (libN magmaBad) 4 "MagmaN" = false := by decide


/-! ### A view out of a theory with structures -/

/-- `Bimagma → NatArith`: both copies of `Magma` go to addition. -/
def bimagmaView : View :=
  { dom := "Bimagma", cod := "NatArith",
    assign := [(.sub "add" "Magma" "U", N), (.sub "add" "Magma" "op", .const gPlus),
               (.sub "mul" "Magma" "U", N), (.sub "mul" "Magma" "op", .const gPlus)] }

theorem bimagmaView_checks : checkView lib 4 bimagmaView = true := by decide

theorem bimagmaView_wellTyped : bimagmaView.WellTyped LF.foundation lib :=
  checkView_sound bimagmaView_checks

/-- Forgetting to assign `mul/op` is caught: the copy would be mapped to itself, which is
not a constant of `NatArith`. -/
def bimagmaViewPartial : View :=
  { dom := "Bimagma", cod := "NatArith",
    assign := [(.sub "add" "Magma" "U", N), (.sub "add" "Magma" "op", .const gPlus),
               (.sub "mul" "Magma" "U", N)] }

theorem bimagmaViewPartial_rejected : checkView lib 4 bimagmaViewPartial = false := by decide

end MMT.Example
