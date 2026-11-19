/-!
# MMT terms

This file formalizes the object level of MMT (`api/objects/Obj.scala`).

MMT terms are OpenMath-style:
* `OMV`     — bound variables, here represented by de Bruijn indices (`Term.var`);
* `OMS/OMID` — references to constants by their global name (`Term.const`);
* `OMA`     — application (`Term.app`); n-ary `OMA(f, a₁,…,aₙ)` is represented curried;
* `OMBIND`  — binding (`Term.bind binder tp body`), binding one typed variable
  in `body`; multi-variable contexts are represented by nesting.

Literals, attributions, and semi-formal objects are omitted: they are inert with
respect to everything formalized here (they contain neither constants nor variables).
-/

namespace MMT

/-- Names of modules (theories, views). In MMT these are `MPath`s. -/
abbrev ThyName := String

/-- Local names of constants (MMT `LocalName`). `sub s S c` is the copy of the
constant `S?c` induced by the structure `s` (MMT: the complex name `[S]/s/c`). -/
inductive LName where
  /-- A base name. -/
  | base (n : String)
  /-- The copy of the constant `thy?orig` induced by the structure `s`. -/
  | sub  (s : String) (thy : ThyName) (orig : LName)
deriving DecidableEq, Repr, Inhabited

instance : Coe String LName := ⟨LName.base⟩

/-- Global names of constants (MMT `GlobalName = MPath ? LocalName`). -/
structure GName where
  /-- The home theory. -/
  thy  : ThyName
  /-- The local name. -/
  name : LName
deriving DecidableEq, Repr, Inhabited

/-- MMT terms. -/
inductive Term where
  /-- A bound variable (de Bruijn index). -/
  | var   (i : Nat)
  /-- A constant, by global name. -/
  | const (c : GName)
  /-- Application. -/
  | app   (f a : Term)
  /-- Binding: binder, type of the bound variable, body. -/
  | bind  (binder tp body : Term)
deriving DecidableEq, Repr, Inhabited

namespace Term

/-! ## de Bruijn operations -/

/-- `liftN k c t` shifts every variable `≥ c` in `t` by `k`. -/
def liftN (k : Nat) : Nat → Term → Term
  | c, var i      => if i < c then var i else var (i + k)
  | _, const n    => const n
  | c, app f a    => app (liftN k c f) (liftN k c a)
  | c, bind b A t => bind (liftN k c b) (liftN k c A) (liftN k (c + 1) t)

/-- `inst j u t` substitutes `u` for variable `j` in `t` (and lowers variables above `j`). -/
def inst (j : Nat) (u : Term) : Term → Term
  | var i      => if i < j then var i else if i = j then liftN j 0 u else var (i - 1)
  | const n    => const n
  | app f a    => app (inst j u f) (inst j u a)
  | bind b A t => bind (inst j u b) (inst j u A) (inst (j + 1) u t)

/-- `ClosedAt n t`: all free variables of `t` are `< n`. `ClosedAt 0` means closed. -/
def ClosedAt : Nat → Term → Prop
  | n, var i      => i < n
  | _, const _    => True
  | n, app f a    => ClosedAt n f ∧ ClosedAt n a
  | n, bind b A t => ClosedAt n b ∧ ClosedAt n A ∧ ClosedAt (n + 1) t

theorem ClosedAt.mono {n m : Nat} {t : Term} (h : ClosedAt n t) (hnm : n ≤ m) : ClosedAt m t := by
  induction t generalizing n m with
  | var i => simp only [ClosedAt] at *; omega
  | const _ => trivial
  | app f a ihf iha => exact ⟨ihf h.1 hnm, iha h.2 hnm⟩
  | bind b A t ihb ihA iht => exact ⟨ihb h.1 hnm, ihA h.2.1 hnm, iht h.2.2 (by omega)⟩

/-- Lifting above the closure bound does nothing. -/
theorem liftN_closedAt {k n c : Nat} {t : Term} (h : ClosedAt n t) (hc : n ≤ c) :
    liftN k c t = t := by
  induction t generalizing n c with
  | var i =>
    simp only [ClosedAt] at h
    have : i < c := by omega
    simp [liftN, this]
  | const _ => rfl
  | app f a ihf iha => simp [liftN, ihf h.1 hc, iha h.2 hc]
  | bind b A t ihb ihA iht =>
    simp [liftN, ihb h.1 hc, ihA h.2.1 hc, iht h.2.2 (by omega : n + 1 ≤ c + 1)]

/-- Substituting above the closure bound does nothing. -/
theorem inst_closedAt {j n : Nat} {u t : Term} (h : ClosedAt n t) (hj : n ≤ j) :
    inst j u t = t := by
  induction t generalizing n j with
  | var i =>
    simp only [ClosedAt] at h
    have : i < j := by omega
    simp [inst, this]
  | const _ => rfl
  | app f a ihf iha => simp [inst, ihf h.1 hj, iha h.2 hj]
  | bind b A t ihb ihA iht =>
    simp [inst, ihb h.1 hj, ihA h.2.1 hj, iht h.2.2 (by omega : n + 1 ≤ j + 1)]

theorem liftN_closed {k c : Nat} {t : Term} (h : ClosedAt 0 t) : liftN k c t = t :=
  liftN_closedAt h (Nat.zero_le _)

theorem inst_closed {j : Nat} {u t : Term} (h : ClosedAt 0 t) : inst j u t = t :=
  inst_closedAt h (Nat.zero_le _)

end Term
end MMT
