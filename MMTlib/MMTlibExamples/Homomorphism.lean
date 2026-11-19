import MMTlibExamples.Algebra
import MMTlib.Diagrams.Homomorphism.Views
import MMTlib.Diagrams.Homomorphism.Predicates
import MMTlib.Diagrams.Homomorphism.Axioms

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

/-! ### Ordered magmas: a predicate

An ordered magma adds `le : U U`. `Hom` declares
`le^h : Π x y : U¹. ded (le¹ x y) → ded (le² (U^h x) (U^h y))`. -/

def orderPreds : Hom.Preds magmaFO where
  pred? n := if n = "le" then some ["U", "U"] else none
  not_sort n as h := by
    by_cases hn : n = "le"
    · subst hn; decide
    · simp [hn] at h
  not_op n as h := by
    by_cases hn : n = "le"
    · subst hn; simp [magmaFO]
    · simp [hn] at h
  sorts n as h := by
    by_cases hn : n = "le"
    · simp [hn] at h; subst h; simp [magmaFO]
    · simp [hn] at h

/-- The preservation axiom for `le` is well-typed. -/
theorem hom_le_typed :
    Hom.D (Hom.homSigP "HomOMagma" magmaFO orderPreds)
      (.typing [] (Hom.predAx "HomOMagma" magmaFO "le" ["U", "U"]) LF.type) :=
  Hom.predAx_typed (by decide) (by simp [orderPreds])

/-! ### Semigroups: an equational axiom

Associativity `assoc : ∀ x y z. (x·y)·z = x·(y·z)`, with `x = var 2`, `y = var 1`,
`z = var 0`. `Hom(Semigroup)` contains a copy of it for each model. -/

def opT (a b : Hom.FOT) : Hom.FOT := .app (.app (.cnst "op") a) b

def assocL : Hom.FOT := opT (opT (.var 2) (.var 1)) (.var 0)
def assocR : Hom.FOT := opT (.var 2) (opT (.var 1) (.var 0))

theorem op_ws {a b : Hom.FOT} (ha : Hom.WS magmaFO ["U", "U", "U"] a [] "U")
    (hb : Hom.WS magmaFO ["U", "U", "U"] b [] "U") :
    Hom.WS magmaFO ["U", "U", "U"] (opT a b) [] "U" :=
  .app (.app (.cnst (by simp [magmaFO])) ha) hb

theorem var_ws {i : Nat} (hi : i < 3) : Hom.WS magmaFO ["U", "U", "U"] (.var i) [] "U" :=
  .var (by match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl)

def semigroupAx : Hom.EqAxioms magmaFO where
  ax? n := if n = "assoc" then some (["U", "U", "U"], assocL, assocR, "U") else none
  not_sort n a h := by
    by_cases hn : n = "assoc"
    · subst hn; decide
    · simp [hn] at h
  not_op n a h := by
    by_cases hn : n = "assoc"
    · subst hn; simp [magmaFO]
    · simp [hn] at h
  sorts n as s t b h := by
    by_cases hn : n = "assoc"
    · simp [hn] at h; obtain ⟨rfl, -⟩ := h; simp [magmaFO]
    · simp [hn] at h
  lhs n as s t b h := by
    by_cases hn : n = "assoc"
    · simp [hn] at h; obtain ⟨rfl, rfl, -, rfl⟩ := h
      exact op_ws (op_ws (var_ws (by decide)) (var_ws (by decide))) (var_ws (by decide))
    · simp [hn] at h
  rhs n as s t b h := by
    by_cases hn : n = "assoc"
    · simp [hn] at h; obtain ⟨rfl, -, rfl, rfl⟩ := h
      exact op_ws (var_ws (by decide)) (op_ws (var_ws (by decide)) (var_ws (by decide)))
    · simp [hn] at h

/-- The copy of associativity in the second model is well-typed in `Hom(Semigroup)`. -/
theorem hom_assoc_typed :
    Hom.D (Hom.homSigA "HomSemigroup" magmaFO semigroupAx)
      (.typing [] (Hom.eqAx "HomSemigroup" magmaFO "2" ["U", "U", "U"] assocL assocR "U") LF.type) :=
  Hom.eqAx_typed (n := "assoc") (by decide) (.inr rfl) (by simp [semigroupAx])

end MMT.Example
