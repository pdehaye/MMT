import MMTlibExamples.Algebra
import MMTlib.Diagrams.Homomorphism.Views

/-!
# The homomorphism functor on magmas

`Hom(Magma)` and the homomorphism functor applied to a view that sends an operation to
a compound term.
-/

namespace MMT.Example

open LF

/-! ### The homomorphism functor on magmas

`Hom(Magma)` declares `U¹, U², U^h : U¹ → U²`, `op¹, op²`, and
`op^h : Π x y : U¹. ded (U^h (op¹ x y) = op² (U^h x) (U^h y))`. -/

/-- Magmas as a first-order signature. -/
def magmaFO : Hom.FOSig where
  thy := "MagmaFO"
  isSort n := n == "U"
  op? n := if n = "op" then some (["U", "U"], "U") else none
  sort_not_op n h := by simp at h; subst h; decide
  op_sorts f as b h := by
    by_cases hf : f = "op"
    · simp [hf] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · simp [hf] at h
  thy_ne_sfol := by decide
  thy_ne_lf := by decide

/-- The homomorphism axiom for `op` is well-typed in `Hom(Magma)`. -/
theorem hom_op_typed :
    Hom.D (Hom.homSig "HomMagma" magmaFO)
      (.typing [] (Hom.homAx "HomMagma" magmaFO "op" ["U", "U"] "U") LF.type) :=
  Hom.homAx_typed (by decide) (by simp [magmaFO])

/-- The axiom is literally `Π x:U¹. Π y:U¹. ded (eq U² (U^h (op¹ x y)) (op² (U^h x) (U^h y)))`. -/
example : Hom.homAx "HomMagma" magmaFO "op" ["U", "U"] "U" =
    let c (k n : String) : Term := .const ⟨"HomMagma", .sub k "MagmaFO" n⟩
    LF.Pi (c "1" "U") (LF.Pi (c "1" "U")
      (Hom.ded (Hom.eqT (c "2" "U")
        (.app (c "h" "U") (.app (.app (c "1" "op") (.var 1)) (.var 0)))
        (.app (.app (c "2" "op") (.app (c "h" "U") (.var 1))) (.app (c "h" "U") (.var 0)))))) :=
  rfl

/-! ### The homomorphism functor on a view with a compound term

`Nat` has `N`, `plus : N → N → N` and `zero : N`. The view `Magma → Nat` sends
`U ↦ N` and `op ↦ λ x y. plus x (plus y zero)`. `Hom` of this view sends `op^h` to a proof
built from `plus^h`, `zero^h`, `refl`, `trans` and `cong`, and it is a well-typed
morphism `Hom(Magma) → Hom(Nat)`. -/

def natFO : Hom.FOSig where
  thy := "NatFO"
  isSort n := n == "N"
  op? n := if n = "plus" then some (["N", "N"], "N")
    else if n = "zero" then some ([], "N") else none
  sort_not_op n h := by simp at h; subst h; decide
  op_sorts f as b h := by
    by_cases h1 : f = "plus"
    · simp [h1] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · by_cases h2 : f = "zero"
      · simp [h2] at h; obtain ⟨rfl, rfl⟩ := h; simp
      · simp [h1, h2] at h
  thy_ne_sfol := by decide
  thy_ne_lf := by decide

/-- `plus x (plus y zero)` with `x = var 1`, `y = var 0`. -/
def opImage : Hom.FOT :=
  .app (.app (.cnst "plus") (.var 1)) (.app (.app (.cnst "plus") (.var 0)) (.cnst "zero"))

def plusZeroView : Hom.FOView magmaFO natFO where
  sort _ := "N"
  sortOk _ _ := by decide
  opT _ := opImage
  opOk f as b h := by
    by_cases hf : f = "op"
    · simp [magmaFO, hf] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp : natFO.op? "plus" = some (["N", "N"], "N") := by simp [natFO]
      have hz : natFO.op? "zero" = some ([], "N") := by simp [natFO]
      exact .app (.app (.cnst hp) (.var rfl)) (.app (.app (.cnst hp) (.var rfl)) (.cnst hz))
    · simp [magmaFO, hf] at h

/-- `Hom(plusZeroView) : Hom(Magma) → Hom(Nat)` is a well-typed morphism. -/
theorem hom_plusZeroView :
    IsMorphism LF.foundation (Hom.homSig "HomMagma" magmaFO) (Hom.homSig "HomNat" natFO)
      (plusZeroView.hom "HomMagma" "HomNat") :=
  Hom.FOView.hom_isMorphism (by decide) (by decide) (by decide)

end MMT.Example
