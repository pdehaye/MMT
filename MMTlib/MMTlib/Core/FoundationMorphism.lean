import MMTlib.Core.Judgment

/-!
# Foundation morphisms

MMT relates foundations (logics) by translating their meta-theories. A *foundation
morphism* `F₁ → F₂` translates the meta-symbols of `F₁` so that every rule of `F₁`
becomes derivable in `F₂`. It then transports every derivation (`FMor.preserves`) over
the translated signature (`Sig.transSig`).
-/

namespace MMT

/-! ## Foundation morphisms -/

/-- A signature translated along `φ`: same constants, translated declarations. -/
def Sig.transSig (S : Sig) (φ : Subst) : Sig := fun c =>
  (S c).map fun i => ⟨i.tp.map (·.trans φ), i.df.map (·.trans φ)⟩

/-- A foundation morphism `F₁ → F₂`: a translation of the meta-symbols of `F₁`, fixing all
other constants, under which every rule of `F₁` is derivable in `F₂` (over signatures
satisfying `P`). -/
structure FMor (F₁ F₂ : Foundation) (P : Sig → Prop) where
  φ : Subst
  closed : φ.Closed
  fix : ∀ c, ¬ F₁.metaSym c → φ c = .const c
  rules : ∀ S, P S → ∀ {ps j}, F₁.Rule ps j →
    (∀ p ∈ ps, Derivable F₂ (S.transSig φ) (p.trans φ)) →
    Derivable F₂ (S.transSig φ) (j.trans φ)

/-- **Foundation morphisms transport derivations.** Signature constants must not be
meta-symbols of the source foundation. -/
theorem FMor.preserves {F₁ F₂ : Foundation} {P : Sig → Prop} (m : FMor F₁ F₂ P) {S : Sig}
    (hP : P S) (hS : ∀ c i, S c = some i → ¬ F₁.metaSym c) {J : Judgment}
    (h : Derivable F₁ S J) : Derivable F₂ (S.transSig m.φ) (J.trans m.φ) := by
  induction h with
  | @const Γ c A d hc =>
    rw [Judgment.trans, Term.trans, m.fix c (hS c _ hc)]
    exact .const (d := d.map (·.trans m.φ)) (by simp [Sig.transSig, hc])
  | @defn Γ c A d hc =>
    rw [Judgment.trans, Term.trans, m.fix c (hS c _ hc)]
    exact .defn (by simp [Sig.transSig, hc])
  | rule hr _ ih => exact m.rules S hP hr ih

end MMT
