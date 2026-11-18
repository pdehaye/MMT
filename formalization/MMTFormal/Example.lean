import MMTFormal.LF
import MMTFormal.Modules

/-!
# Example: a view from magmas to natural-number arithmetic

```mmt
theory LF = type ❘ kind ❘ Pi ❘ lambda ❙
theory Magma : LF = U : type ❙ op : U → U → U ❙ ❚
theory NatArith : LF = N : type ❙ zero : N ❙ plus : N → N → N ❙ ❚
view Plus : Magma -> NatArith = U = N ❙ op = plus ❙ ❚
```

We check the view, derive `x : U ⊢ op x x : U` in `Magma`, and obtain
`x : N ⊢ plus x x : N` in `NatArith` from the preservation theorem.
-/

namespace MMT.Example

open LF

def gU    : GName := ⟨"Magma", "U"⟩
def gOp   : GName := ⟨"Magma", "op"⟩
def gN    : GName := ⟨"NatArith", "N"⟩
def gZero : GName := ⟨"NatArith", "zero"⟩
def gPlus : GName := ⟨"NatArith", "plus"⟩

def U : Term := .const gU
def N : Term := .const gN

def lfThy : Theory :=
  { metaThy := none,
    decls := [.const "type" none none, .const "kind" none none,
              .const "Pi" none none, .const "lambda" none none] }

def magma : Theory :=
  { metaThy := some "LF",
    decls := [.const "U" (some type) none, .const "op" (some (arrow U (arrow U U))) none] }

def natArith : Theory :=
  { metaThy := some "LF",
    decls := [.const "N" (some type) none, .const "zero" (some N) none,
              .const "plus" (some (arrow N (arrow N N))) none] }

def lib : Library := fun
  | "LF" => some lfThy
  | "Magma" => some magma
  | "NatArith" => some natArith
  | _ => none

def plusView : View :=
  { dom := "Magma", cod := "NatArith", assign := [("U", N), ("op", .const gPlus)] }

/-! ### Visibility in the example graph -/

theorem visible_LF {R : ThyName} (h : Visible lib "LF" R) : R = "LF" := by
  cases h with
  | refl => rfl
  | incl hT hS _ => simp [lib] at hT; subst hT; simp [lfThy] at hS
  | metaThy hT hM _ => simp [lib] at hT; subst hT; simp [lfThy] at hM

theorem visible_from_meta {T : ThyName} {th : Theory} (hT : lib T = some th)
    (hm : th.metaThy = some "LF") (hi : ∀ S, Decl.incl S ∉ th.decls)
    {R : ThyName} (h : Visible lib T R) : R = T ∨ R = "LF" := by
  cases h with
  | refl => exact .inl rfl
  | incl hT' hS _ => rw [hT] at hT'; cases hT'; exact absurd hS (hi _)
  | metaThy hT' hM hv =>
    rw [hT] at hT'; cases hT'; rw [hm] at hM; cases hM; exact .inr (visible_LF hv)

theorem visible_magma {R : ThyName} (h : Visible lib "Magma" R) : R = "Magma" ∨ R = "LF" :=
  visible_from_meta rfl rfl (by simp [magma]) h

theorem natArith_sees_LF : Visible lib "NatArith" "LF" := .metaThy rfl rfl (.refl _)

/-! ### Derivation helpers -/

abbrev D := Derivable LF.foundation

theorem rule0 {S j} (h : LF.Rule [] j) : D S j := .rule h (by simp)
theorem rule1 {S p j} (h : LF.Rule [p] j) (hp : D S p) : D S j := .rule h (by simpa using hp)
theorem rule2 {S p q j} (h : LF.Rule [p, q] j) (hp : D S p) (hq : D S q) : D S j :=
  .rule h (by simp; exact ⟨hp, hq⟩)

theorem flat_local {T : ThyName} {th : Theory} {n : String} {i : ConstInfo}
    (hT : lib T = some th) (hl : th.localLookup n = some i) : flat lib T ⟨T, n⟩ = some i :=
  flat_eq_some.mpr ⟨.refl _, by simp [hT, hl]⟩

/-! ### Checking the view -/

theorem lf_lookup {n : String} {i : ConstInfo} (h : lfThy.localLookup n = some i) :
    i = ⟨none, none⟩ := by
  simp [lfThy, Theory.localLookup] at h
  by_cases h1 : "type" = n <;> by_cases h2 : "kind" = n <;>
    by_cases h3 : "Pi" = n <;> by_cases h4 : "lambda" = n <;> simp_all

theorem magma_lookup {n : String} {i : ConstInfo} (h : magma.localLookup n = some i) :
    (n = "U" ∧ i = ⟨some type, none⟩) ∨ (n = "op" ∧ i = ⟨some (arrow U (arrow U U)), none⟩) := by
  simp [magma, Theory.localLookup] at h
  by_cases h1 : "U" = n <;> by_cases h2 : "op" = n <;> simp_all

theorem plusView_wellTyped : plusView.WellTyped LF.foundation lib := by
  apply View.isMorphism_of_check
  · intro p hp; simp [plusView] at hp; rcases hp with rfl | rfl <;> trivial
  · intro c hc; simp [LF.foundation, LF.thy] at hc; simp [plusView, hc]
  · intro n A d h
    obtain ⟨-, hl⟩ := flat_eq_some.mp h
    change magma.localLookup n = _ at hl
    rcases magma_lookup hl with ⟨rfl, hi⟩ | ⟨rfl, hi⟩ <;> cases hi <;>
      exact ⟨.const (d := none) (flat_local (th := natArith) rfl (by decide)), by simp⟩
  · intro c i hne h
    obtain ⟨hv, hl⟩ := flat_eq_some.mp h
    rcases visible_magma hv with h' | h'
    · exact absurd h' hne
    · obtain ⟨t, n⟩ := c
      simp only at h'; subst h'
      change lfThy.localLookup n = _ at hl
      cases lf_lookup hl
      exact ⟨flat_eq_some.mpr ⟨natArith_sees_LF, hl⟩, by simp, by simp⟩

/-! ### A derivation in `Magma` and its translation -/

/-- `x : U ⊢ op x x : U` in `Magma`. -/
theorem magma_op_xx :
    D (flat lib "Magma") (.typing [U] (.app (.app (.const gOp) (.var 0)) (.var 0)) U) := by
  have hop : D (flat lib "Magma") (.typing [U] (.const gOp) (Pi U (Pi U U))) :=
    .const (d := none) (flat_local (th := magma) rfl (by decide))
  have hx : D (flat lib "Magma") (.typing [U] (.var 0) U) := rule0 (LF.Rule.var [U] 0 U rfl)
  have h1 : D (flat lib "Magma") (.typing [U] (.app (.const gOp) (.var 0)) (Pi U U)) :=
    rule2 (LF.Rule.appE [U] U (Pi U U) (.const gOp) (.var 0)) hop hx
  exact rule2 (LF.Rule.appE [U] U U _ (.var 0)) h1 hx

/-- By judgment preservation along the view: `x : N ⊢ plus x x : N` in `NatArith`. -/
theorem natArith_plus_xx :
    D (flat lib "NatArith") (.typing [N] (.app (.app (.const gPlus) (.var 0)) (.var 0)) N) :=
  plusView_wellTyped.preserves magma_op_xx

end MMT.Example
