import MMTlib.Diagrams.Homomorphism.Views

/-!
# The homomorphism functor for equational theories

Extends `Hom(Σ)` to signatures with *equational axioms* `ax : ∀ x⃗:a⃗. s = t` (e.g.
associativity). Homomorphisms go between two models, and both models satisfy the
axioms, so `Hom(Σ)` contains a copy of every axiom for each model:

```
  ax¹ : Π x⃗:a⃗¹. ded (s¹ = t¹),   ax² : Π x⃗:a⃗². ded (s² = t²)
```

There is no homomorphism condition for axioms.

Main results:
* `eqAx_typed`, `homSigA_wf`: every declaration of `Hom(Σ)` with axioms is well-typed;
* `FOMorA.hom_isMorphism`: signature morphisms that map axioms to axioms (with the
  renamed statement) induce well-typed morphisms `Hom(Σ) → Hom(Σ')`.
-/

namespace MMT.Hom

open LF Term Judgment

/-- Equational axioms over a first-order signature: variable sorts (`var i` has sort
`as.reverse[i]`), the two sides, and their sort. -/
structure EqAxioms (Sg : FOSig) where
  ax? : String → Option (List String × FOT × FOT × String)
  not_sort : ∀ n a, ax? n = some a → Sg.isSort n = false
  not_op : ∀ n a, ax? n = some a → Sg.op? n = none
  sorts : ∀ n as s t b, ax? n = some (as, s, t, b) → ∀ a ∈ as, Sg.isSort a = true
  lhs : ∀ n as s t b, ax? n = some (as, s, t, b) → WS Sg as.reverse s [] b
  rhs : ∀ n as s t b, ax? n = some (as, s, t, b) → WS Sg as.reverse t [] b

variable (H : ThyName)

/-- The statement of the copy `axᵏ`. -/
def eqAx (Sg : FOSig) (k : String) (as : List String) (s t : FOT) (b : String) : Term :=
  arrows (as.map (cs H k Sg))
    (ded (eqT (cs H k Sg b) (enc H Sg k Term.var s) (enc H Sg k Term.var t)))

/-- The declarations of the copies of an axiom. -/
def axInfo (Sg : FOSig) (E : EqAxioms Sg) (k n : String) : Option ConstInfo :=
  (E.ax? n).bind fun ⟨as, s, t, b⟩ =>
    if k = "1" ∨ k = "2" then some ⟨some (eqAx H Sg k as s t b), none⟩ else none

/-- `Hom(Σ)` for a signature with equational axioms. -/
def homSigA (Sg : FOSig) (E : EqAxioms Sg) : Sig := fun d =>
  if d.thy = H then
    match d.name with
    | .sub k thy (.base n) =>
      if thy = Sg.thy then (axInfo H Sg E k n).or (homInfo H Sg k n) else none
    | _ => none
  else metaSig d

variable {H}

theorem axInfo_none {Sg : FOSig} {E : EqAxioms Sg} {k n : String} (h : E.ax? n = none) :
    axInfo H Sg E k n = none := by simp [axInfo, h]

theorem homInfo_ax_none {Sg : FOSig} {E : EqAxioms Sg} {k n : String} {a}
    (h : E.ax? n = some a) : homInfo H Sg k n = none := by
  simp [homInfo, E.not_sort n a h, E.not_op n a h]

theorem homSigA_cp {Sg : FOSig} {E : EqAxioms Sg} {k n : String} :
    homSigA H Sg E (cp H k Sg n) = (axInfo H Sg E k n).or (homInfo H Sg k n) := by
  simp [homSigA, cp]

theorem homSigA_meta {Sg : FOSig} {E : EqAxioms Sg} {c : GName} (h : c.thy ≠ H) :
    homSigA H Sg E c = metaSig c := by simp [homSigA, h]

/-- The extension is conservative. -/
theorem homSig_sub_homSigA {Sg : FOSig} (E : EqAxioms Sg) : (homSig H Sg).Sub (homSigA H Sg E) := by
  intro c i h
  rcases homSig_cases h with ⟨k, n, rfl, hi⟩ | ⟨hne, hm⟩
  · rw [homSigA_cp]
    cases hp : E.ax? n with
    | none => rw [axInfo_none hp]; simpa using hi
    | some a => rw [homInfo_ax_none hp] at hi; cases hi
  · rw [homSigA_meta hne]; exact hm

theorem homSigA_cases {Sg : FOSig} {E : EqAxioms Sg} {c : GName} {i : ConstInfo}
    (h : homSigA H Sg E c = some i) :
    (∃ k n a, c = cp H k Sg n ∧ E.ax? n = some a ∧ axInfo H Sg E k n = some i) ∨
    homSig H Sg c = some i := by
  obtain ⟨t, nm⟩ := c
  unfold homSigA at h
  by_cases ht : t = H
  · subst ht
    simp only [↓reduceIte] at h
    split at h
    · rename_i k thy n
      split at h
      · subst_vars
        cases hp : E.ax? n with
        | none =>
          rw [axInfo_none hp] at h
          refine .inr ?_
          show homSig _ Sg (cp _ k Sg n) = some i
          rw [homSig_cp]; simpa using h
        | some a =>
          rw [homInfo_ax_none hp] at h
          exact .inl ⟨k, n, a, rfl, hp, by simpa using h⟩
      · cases h
    · cases h
  · simp only [ht, ↓reduceIte] at h
    exact .inr (by rw [homSig_meta ht]; exact h)

theorem homSigA_df {Sg : FOSig} {E : EqAxioms Sg} {c : GName} {i : ConstInfo}
    (h : homSigA H Sg E c = some i) : i.df = none := by
  rcases homSigA_cases h with ⟨k, n, ⟨as, s, t, b⟩, -, hp, hi⟩ | h
  · unfold axInfo at hi
    rw [hp] at hi
    simp only [Option.bind_some] at hi
    split at hi
    · cases hi; rfl
    · cases hi
  · exact homSig_df h

/-! ## Well-typedness -/

section WF

variable {Sg : FOSig} {E : EqAxioms Sg} (hH : H ≠ sfol)
include hH

omit hH in
theorem liftA {J : Judgment} (h : D (homSig H Sg) J) : D (homSigA H Sg E) J :=
  h.mono (homSig_sub_homSigA E)

/-- **Each copy of an axiom is well-typed.** -/
theorem eqAx_typed {k n : String} {as : List String} {s t : FOT} {b : String}
    (hk : k = "1" ∨ k = "2") (hp : E.ax? n = some (as, s, t, b)) :
    D (homSigA H Sg E) (.typing [] (eqAx H Sg k as s t b) type) := by
  have has := E.sorts n as s t b hp
  have hs := E.lhs n as s t b hp
  have ht := E.rhs n as s t b hp
  have hb : Sg.isSort b = true := (hs.sorts hH (Γ := (as.map (cs H "1" Sg)).reverse)
    (fun i s' hi => by simpa using ctx_lookup (H := H) (Sg := Sg) (k := "1") (Γ₀ := []) hi)
    (fun i s' hi => has s' (List.mem_reverse.mp (List.mem_of_getElem? hi)))).2
  apply arrows_typed
  · intro a ha Γ'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact liftA (sort_typed hk (has x hx) Γ')
  · simp only [List.append_nil]
    let Γ := (as.map (cs H k Sg)).reverse
    have hρ : ∀ i s', as.reverse[i]? = some s' →
        D (homSig H Sg) (.typing Γ (Term.var i) (cs H k Sg s')) := fun i s' hi =>
      r0 (LF.Rule.var _ _ _ (by simpa using ctx_lookup (H := H) (Sg := Sg) (k := k) (Γ₀ := []) hi))
    have hS : D (homSig H Sg) (.typing Γ (enc H Sg k Term.var s) (cs H k Sg b)) := by
      simpa [arrows] using enc_typed' hk hρ hs
    have hT : D (homSig H Sg) (.typing Γ (enc H Sg k Term.var t) (cs H k Sg b)) := by
      simpa [arrows] using enc_typed' hk hρ ht
    have heq : D (homSig H Sg) (.typing Γ (.const eqN) (Pi type (Pi (.var 0) (Pi (.var 1) prop)))) :=
      meta_typed hH (d := none) (by simp [metaSig, eqN, propN, dedN]) Γ
    have hded : D (homSig H Sg) (.typing Γ (.const dedN) (Pi prop type)) :=
      meta_typed hH (d := none) (by simp [metaSig, propN, dedN]) Γ
    have e1 : D (homSig H Sg) (.typing Γ (.app (.const eqN) (cs H k Sg b))
        (Pi (cs H k Sg b) (Pi (cs H k Sg b) prop))) :=
      appE' heq (sort_typed hk hb Γ) rfl
    have e2 := appE' (C := Pi (cs H k Sg b) prop) e1 hS rfl
    have e3 := appE' (C := prop) e2 hT rfl
    exact liftA (appE' hded e3 rfl)

/-- **`Hom(Σ)` with axioms is well-formed.** -/
theorem homSigA_wf {k n : String} {A : Term} {d : Option Term}
    (h : homSigA H Sg E (cp H k Sg n) = some ⟨some A, d⟩) :
    A = type ∨ D (homSigA H Sg E) (.typing [] A type) := by
  rcases homSigA_cases h with ⟨k', n', ⟨as, s, t, b⟩, he, hp, hi⟩ | h'
  · simp only [cp, GName.mk.injEq, LName.sub.injEq, LName.base.injEq, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    unfold axInfo at hi
    rw [hp] at hi
    simp only [Option.bind_some] at hi
    split at hi
    · rename_i hk
      simp only [Option.some.injEq, ConstInfo.mk.injEq] at hi
      obtain ⟨rfl, -⟩ := hi
      exact .inr (eqAx_typed hH hk hp)
    · cases hi
  · rcases homSig_wf hH h' with h'' | h''
    · exact .inl h''
    · exact .inr (liftA h'')

end WF

/-! ## Signature morphisms with axioms -/

/-- Renaming the symbols of a first-order term. -/
def FOT.rename (φ : String → String) : FOT → FOT
  | .var i => .var i
  | .cnst g => .cnst (φ g)
  | .app f x => .app (FOT.rename φ f) (FOT.rename φ x)

/-- A signature morphism that maps axioms to axioms with the renamed statement. -/
structure FOMorA {Sg Sg' : FOSig} (E : EqAxioms Sg) (E' : EqAxioms Sg') extends FOMor Sg Sg' where
  ax : ∀ n as s t b, E.ax? n = some (as, s, t, b) →
    E'.ax? (φ n) = some (as.map φ, s.rename φ, t.rename φ, φ b)

namespace FOMorA

variable {Sg Sg' : FOSig} {E : EqAxioms Sg} {E' : EqAxioms Sg'} (μ : FOMorA E E') {H H' : ThyName}

theorem enc_trans (k : String) (s : FOT) :
    (enc H Sg k Term.var s).trans (μ.hom H H') = enc H' Sg' k Term.var (s.rename μ.φ) := by
  induction s with
  | var => rfl
  | cnst g => exact FOMor.hom_cs
  | app f x ihf ihx => simp [enc, Term.trans, ihf, ihx, FOT.rename]

theorem hom_eqAx (hH : H ≠ sfol) (hL : H ≠ LF.thy) (k : String) (as : List String) (s t : FOT)
    (b : String) :
    (eqAx H Sg k as s t b).trans (μ.hom H H') =
      eqAx H' Sg' k (as.map μ.φ) (s.rename μ.φ) (t.rename μ.φ) (μ.φ b) := by
  have hP : μ.hom H H' piN = .const piN := FOMor.hom_fix hH hL (.inr rfl)
  have hD : μ.hom H H' dedN = .const dedN := FOMor.hom_fix hH hL (.inl rfl)
  have hE : μ.hom H H' eqN = .const eqN := FOMor.hom_fix hH hL (.inl rfl)
  simp [eqAx, arrows_trans hP, ded, eqT, Term.trans, hD, hE, FOMor.hom_cs, μ.enc_trans,
    Function.comp_def]

/-- **`Hom(φ)` is a well-typed morphism** between the theories of homomorphisms of
equational theories. -/
theorem hom_isMorphism (hH : H ≠ sfol) (hL : H ≠ LF.thy) (hH' : H' ≠ sfol) :
    IsMorphism LF.foundation (homSigA H Sg E) (homSigA H' Sg' E') (μ.hom H H') where
  closed d := by unfold FOMor.hom; repeat (first | split | trivial)
  fixMeta c hc := FOMor.hom_fix hH hL (.inr hc)
  typed {c A d} hc := by
    rcases homSigA_cases hc with ⟨k, n, ⟨as, s, t, b⟩, rfl, hp, hi⟩ | h'
    · rw [FOMor.hom_cp]
      have hp' := μ.ax n as s t b hp
      unfold axInfo at hi
      rw [hp] at hi
      simp only [Option.bind_some] at hi
      refine .const (c := cp H' k Sg' (μ.φ n)) (d := none) ?_
      rw [homSigA_cp]
      unfold axInfo
      rw [hp']
      simp only [Option.bind_some]
      split at hi
      · rename_i hk
        simp only [hk, ↓reduceIte, Option.some.injEq, ConstInfo.mk.injEq] at hi ⊢
        obtain ⟨rfl, rfl⟩ := hi
        simp [μ.hom_eqAx hH hL]
      · cases hi
    · exact ((μ.toFOMor.hom_isMorphism hH hL hH').typed h').mono (homSig_sub_homSigA E')
  defn {c A d} hc := by cases homSigA_df hc

end FOMorA

end MMT.Hom
