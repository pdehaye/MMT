import MMTlibExamples.Algebra
import MMTlib.Checking.Unknowns

/-!
# Unknowns: solving an implicit argument

The implicit argument of `id ?A c : N` is solved by unification, as a solved definition,
and by type reconstruction.
-/

namespace MMT.Example

open LF

/-! ### Solving an implicit argument

With `id : Π A:type. A → A`, `N : type` and `c : N`, the term `id ?A c` is checked
against `N`. Unifying the constraint `?A = N` and checking the instance succeeds, so
`id N c : N` is derivable. -/

def gId : GName := ⟨"Poly", "id"⟩
def gNat : GName := ⟨"Poly", "N"⟩
def gC : GName := ⟨"Poly", "c"⟩
def gA : GName := ⟨unknownThy, "A"⟩

def polySig : Sig := fun x =>
  if x = gId then some ⟨some (LF.Pi LF.type (LF.Pi (.var 0) (.var 1))), none⟩
  else if x = gNat then some ⟨some LF.type, none⟩
  else if x = gC then some ⟨some (.const gNat), none⟩
  else none

def idApp : Term := .app (.app (.const gId) (.const gA)) (.const gC)

theorem solve_idApp :
    (solveCheck polySig 16 [(.const gA, .const gNat)] [] idApp (.const gNat)).isSome = true := by
  decide

/-- The solved and checked judgment: `id N c : N`. -/
theorem idApp_solved :
    Derivable LF.foundation polySig
      (.typing [] (.app (.app (.const gId) (.const gNat)) (.const gC)) (.const gNat)) := by
  obtain ⟨θ, hθ⟩ := Option.isSome_iff_exists.mp solve_idApp
  obtain ⟨hsol, hcs, hd⟩ := solveCheck_sound hθ
  have hA : θ gA = .const gNat := by
    have := hcs _ (List.mem_singleton_self _)
    simpa [Term.trans, hsol.fix gNat (by decide)] using this
  simpa [idApp, Term.trans, hsol.fix gId (by decide), hsol.fix gC (by decide),
    hsol.fix gNat (by decide), hA] using hd

/-- The same, the MMT way: the solved unknown `?A : type := N` is a definition, so checking
`id ?A c : N` unfolds it by δ-conversion; instantiating gives `id N c : N`. -/
theorem idApp_checkSolved :
    checkSolved polySig [⟨.base "A", LF.type, .const gNat⟩] [] idApp (.const gNat) = true := by
  decide


/-! ### Type reconstruction -/

/-- The implicit argument of `id ?A c : N` is reconstructed without user-given
constraints: `?A := N`. -/
theorem idApp_reconstructed :
    (elaborate polySig 16 [] idApp (.const gNat)).map (fun θ => θ gA) = some (.const gNat) := by
  decide

theorem idApp_elaborated :
    Derivable LF.foundation polySig
      (.typing [] (.app (.app (.const gId) (.const gNat)) (.const gC)) (.const gNat)) := by
  cases h : elaborate polySig 16 [] idApp (.const gNat) with
  | none => have := idApp_reconstructed; rw [h] at this; cases this
  | some θ =>
    have hA : θ gA = .const gNat := by
      have := idApp_reconstructed; rw [h] at this; simpa using this
    obtain ⟨hsol, hd⟩ := elaborate_sound h
    simpa [idApp, Term.trans, hsol.fix gId (by decide), hsol.fix gC (by decide),
      hsol.fix gNat (by decide), hA] using hd

end MMT.Example
