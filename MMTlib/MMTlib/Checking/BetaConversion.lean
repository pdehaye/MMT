import MMTlib.Foundations.LF.Confluence

/-!
# Deciding β-conversion

An executable normal-order β-normalizer and a conversion checker built on it.

* `LF.step?` performs one leftmost-outermost β-step, or reports that the term is normal
  (`LF.step?_some`, `LF.step?_none`). This makes `LF.Normal` decidable.
* `LF.nf fuel t` normalizes `t` in at most `fuel` steps (`LF.nf_sound`).
* `LF.conv? fuel t u` compares normal forms. Thanks to confluence the answer is
  correct in both directions: `true` means `t` and `u` are β-convertible, and `false`
  means they are not (`LF.conv?_correct`). It answers `none` when the fuel runs out.

This is the shape of MMT's equality check for LF terms without unknowns or
definitions: compare normal forms. Termination on well-typed terms (strong
normalization) is not formalized, hence the fuel.
-/

namespace MMT.LF

/-- Contract `f a` if `f` is a λ-abstraction. -/
def contract : Term → Term → Option Term
  | .bind (.const c) _ t, a => if c = lamN then some (Term.inst 0 a t) else none
  | _, _ => none

/-- One leftmost-outermost β-step, or `none` if the term is normal. -/
def step? : Term → Option Term
  | .var _ => none
  | .const _ => none
  | .app f a =>
    match contract f a with
    | some u => some u
    | none =>
      match step? f with
      | some f' => some (.app f' a)
      | none => (step? a).map (.app f)
  | .bind b A t =>
    match step? b with
    | some b' => some (.bind b' A t)
    | none =>
      match step? A with
      | some A' => some (.bind b A' t)
      | none => (step? t).map (.bind b A)

theorem contract_some {f a u : Term} (h : contract f a = some u) : Step (.app f a) u := by
  unfold contract at h
  split at h
  · rename_i c A t
    split at h
    · subst_vars
      cases h
      exact Step.beta A t a
    · cases h
  · cases h

theorem contract_none {A t a : Term} (h : contract (lam A t) a = none) : False := by
  simp [contract] at h

/-- `step?` only performs β-steps. -/
theorem step?_some : ∀ {t u : Term}, step? t = some u → Step t u
  | .var _, _, h => by simp [step?] at h
  | .const _, _, h => by simp [step?] at h
  | .app f a, u, h => by
    simp only [step?] at h
    split at h
    · rename_i hc; cases h; exact contract_some hc
    · split at h
      · rename_i hf; cases h; exact .appL a (step?_some hf)
      · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .appR f (step?_some ha)
  | .bind b A t, u, h => by
    simp only [step?] at h
    split at h
    · rename_i hb; cases h; exact .bindB A t (step?_some hb)
    · split at h
      · rename_i hA; cases h; exact .bindA b t (step?_some hA)
      · obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .bindT b A (step?_some ht)

/-- `step?` fails only on normal terms. -/
theorem step?_none : ∀ {t : Term}, step? t = none → Normal t
  | .var _, _, _, h => by cases h
  | .const _, _, _, h => by cases h
  | .app f a, h, u, hs => by
    simp only [step?] at h
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · rename_i hf
        have ha : step? a = none := Option.map_eq_none_iff.mp h
        cases hs with
        | beta A t a => exact contract_none hc
        | appL _ hs => exact step?_none hf _ hs
        | appR _ hs => exact step?_none ha _ hs
  | .bind b A t, h, u, hs => by
    simp only [step?] at h
    split at h
    · cases h
    · rename_i hb
      split at h
      · cases h
      · rename_i hA
        have ht : step? t = none := Option.map_eq_none_iff.mp h
        cases hs with
        | bindB _ _ hs => exact step?_none hb _ hs
        | bindA _ _ hs => exact step?_none hA _ hs
        | bindT _ _ hs => exact step?_none ht _ hs

theorem normal_iff_step?_none {t : Term} : Normal t ↔ step? t = none := by
  constructor
  · intro h
    cases e : step? t with
    | none => rfl
    | some u => exact absurd (step?_some e) (h u)
  · exact step?_none

instance : DecidablePred Normal := fun _ =>
  decidable_of_iff _ normal_iff_step?_none.symm

/-- Normal-order normalization with at most `fuel` steps. -/
def nf : Nat → Term → Option Term
  | 0, _ => none
  | n + 1, t =>
    match step? t with
    | none => some t
    | some u => nf n u

/-- A computed normal form is a normal form of the input. -/
theorem nf_sound : ∀ {n : Nat} {t v : Term}, nf n t = some v → Red t v ∧ Normal v
  | 0, _, _, h => by cases h
  | n + 1, t, v, h => by
    simp only [nf] at h
    split at h
    · rename_i hs; cases h; exact ⟨.refl _, step?_none hs⟩
    · rename_i u hs
      obtain ⟨hr, hn⟩ := nf_sound h
      exact ⟨Star.head (step?_some hs) hr, hn⟩

/-- β-conversion check by comparison of normal forms; `none` if the fuel runs out. -/
def conv? (fuel : Nat) (t u : Term) : Option Bool :=
  match nf fuel t, nf fuel u with
  | some v, some w => some (decide (v = w))
  | _, _ => none

/-- The conversion check is correct in both directions. -/
theorem conv?_correct {fuel : Nat} {t u : Term} {b : Bool} (h : conv? fuel t u = some b) :
    (b = true ↔ Conv t u) := by
  unfold conv? at h
  split at h
  · rename_i v w hv hw
    cases h
    obtain ⟨rv, nv⟩ := nf_sound hv
    obtain ⟨rw, nw⟩ := nf_sound hw
    simp only [decide_eq_true_eq]
    constructor
    · rintro rfl
      exact (Conv.of_red rv).trans (Conv.of_red rw).symm
    · intro hc
      exact Conv.normal_eq ((Conv.of_red rv).symm.trans (hc.trans (Conv.of_red rw))) nv nw
  · cases h

/-- If the check succeeds, the terms are convertible. -/
theorem conv?_true {fuel : Nat} {t u : Term} (h : conv? fuel t u = some true) : Conv t u :=
  (conv?_correct h).mp rfl

/-- If the check fails, the terms are not convertible. -/
theorem conv?_false {fuel : Nat} {t u : Term} (h : conv? fuel t u = some false) :
    ¬ Conv t u :=
  fun hc => Bool.false_ne_true ((conv?_correct h).mpr hc)

end MMT.LF
