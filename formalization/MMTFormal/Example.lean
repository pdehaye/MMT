import MMTFormal.LF
import MMTFormal.Modules
import MMTFormal.Checker
import MMTFormal.HomView

/-!
# Example: a view and structures over LF

```mmt
theory LF = type ❘ kind ❘ Pi ❘ lambda ❙
theory Magma : LF = U : type ❙ op : U → U → U ❙ ❚
theory NatArith : LF = N : type ❙ zero : N ❙ plus : N → N → N ❙ ❚
view Plus : Magma -> NatArith = U = N ❙ op = plus ❙ ❚

theory Bimagma : LF = structure add : Magma ❙ structure mul : Magma ❙ ❚
```

We check the view, derive `x : U ⊢ op x x : U` in `Magma`, and obtain
`x : N ⊢ plus x x : N` in `NatArith` from the preservation theorem. Likewise the
structure `add` yields `x : add/U ⊢ add/op x x : add/U` in `Bimagma`.
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

/-- Two copies of `Magma` via structures. -/
def bimagma : Theory :=
  { metaThy := some "LF", decls := [.struct "add" "Magma" [], .struct "mul" "Magma" []] }

def lib : Library := fun
  | "LF" => some lfThy
  | "Magma" => some magma
  | "NatArith" => some natArith
  | "Bimagma" => some bimagma
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
  flat_eq_some.mpr ⟨.refl _, by simp [homeInfo, hT, hl]⟩

/-! ### Checking the view -/

theorem lf_lookup {n : String} {i : ConstInfo} (h : lfThy.localLookup n = some i) :
    i = ⟨none, none⟩ := by
  simp [lfThy, Theory.localLookup] at h
  by_cases h1 : "type" = n <;> by_cases h2 : "kind" = n <;>
    by_cases h3 : "Pi" = n <;> by_cases h4 : "lambda" = n <;> simp_all

theorem lf_home {n : LName} {i : ConstInfo} (h : homeInfo lib "LF" n = some i) :
    i = ⟨none, none⟩ := by
  cases n with
  | base n => exact lf_lookup h
  | sub s S0 o => simp [homeInfo, lib, lfThy, Theory.structLookup] at h

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
    cases n with
    | sub s S0 o => simp [plusView, homeInfo, lib, magma, Theory.structLookup] at hl
    | base n =>
    change magma.localLookup n = _ at hl
    rcases magma_lookup hl with ⟨rfl, hi⟩ | ⟨rfl, hi⟩ <;> cases hi <;>
      exact ⟨.const (d := none) (flat_local (th := natArith) rfl (by decide)), by simp⟩
  · intro c i hne h
    obtain ⟨hv, hl⟩ := flat_eq_some.mp h
    rcases visible_magma hv with h' | h'
    · exact absurd h' hne
    · obtain ⟨t, n⟩ := c
      simp only at h'; subst h'
      cases lf_home hl
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

/-! ### Structures: `Bimagma` contains two copies of `Magma` -/

def addU : Term := .const ⟨"Bimagma", .sub "add" "Magma" "U"⟩
def addOp : GName := ⟨"Bimagma", .sub "add" "Magma" "op"⟩

theorem visible_bimagma {R : ThyName} (h : Visible lib "Bimagma" R) : R = "Bimagma" ∨ R = "LF" :=
  visible_from_meta rfl rfl (by simp [bimagma]) h

theorem bimagma_not_magma : ¬ Visible lib "Bimagma" "Magma" := by
  intro h; rcases visible_bimagma h with h | h <;> exact absurd h (by decide)

theorem add_struct : (lib "Bimagma").bind (·.structLookup "add") = some ("Magma", []) := by
  simp [lib, bimagma, Theory.structLookup]

theorem addMor_magma (n : LName) :
    structMor lib "Bimagma" "add" ⟨"Magma", n⟩ = .const ⟨"Bimagma", .sub "add" "Magma" n⟩ :=
  structMor_copy bimagma_not_magma

/-- The structure `add : Magma` is a well-typed morphism `Magma → Bimagma`. -/
theorem add_isMorphism :
    IsMorphism LF.foundation (flat lib "Magma") (flat lib "Bimagma")
      (structMor lib "Bimagma" "add") :=
  structMor_isMorphism add_struct
    (fun c hc => by
      simp [LF.foundation, LF.thy] at hc; rw [hc]; exact .metaThy rfl rfl (.refl _))
    (fun c i hc hvis => by
      obtain ⟨hv, hh⟩ := flat_eq_some.mp hc
      rcases visible_magma hv with h' | h'
      · rw [h'] at hvis; exact absurd hvis bimagma_not_magma
      · rw [h'] at hh; cases lf_home hh; exact ⟨by simp, by simp⟩)
    (fun c t h => by simp [List.lookup] at h)

/-- Transported along the structure: `x : add/U ⊢ add/op x x : add/U` in `Bimagma`. -/
theorem bimagma_addop_xx :
    D (flat lib "Bimagma") (.typing [addU] (.app (.app (.const addOp) (.var 0)) (.var 0)) addU) := by
  have := Derivable.trans add_isMorphism magma_op_xx
  simpa [Judgment.trans, Term.trans, U, gU, gOp, addU, addOp, addMor_magma] using this

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
