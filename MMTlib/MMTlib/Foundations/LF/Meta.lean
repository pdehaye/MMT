import MMTlib.Core.Structural
import MMTlib.Foundations.LF.Basic

/-!
# Metatheory of LF

LF's rules are stable under inner weakening and substitution (`LF.Rule.wk`,
`LF.Rule.sub`). The generic results of `MMTlib.Core.Structural` therefore give
weakening (`LF.weaken`) and the substitution lemma (`LF.subst`) for LF. Moreover,
derivable judgments are well-scoped (`LF.scoping`).
-/

namespace MMT

open Term

namespace LF

open Judgment

/-- **Every LF rule is stable under weakening.** -/
theorem Rule.wk {ps : List Judgment} {j : Judgment} (h : Rule ps j) {c : Nat}
    (hc : c ≤ j.ctx.length) (B : Term) :
    ∃ ps', Rule ps' (j.wk c B) ∧ WkPrem ps ps' B := by
  cases h with
  | univ Γ => exact ⟨[], Rule.univ _, by simp [WkPrem]⟩
  | var Γ i A hi =>
    simp only [ctx] at hc
    refine ⟨[], ?_, by simp [WkPrem]⟩
    show Rule [] (typing (ctxIns c B Γ) (liftN 1 c (.var i)) (liftN 1 c (liftN (i + 1) 0 A)))
    by_cases hlt : i < c
    · have hv := Rule.var (ctxIns c B Γ) i _ (ctxIns_lt hlt hi)
      have e : liftN (i + 1) 0 (liftN 1 (c - 1 - i) A) = liftN 1 c (liftN (i + 1) 0 A) := by
        have := Term.liftN_liftN_comm 1 (i + 1) A (c := c - 1 - i) (d := 0) (Nat.zero_le _)
        rw [show c - 1 - i + (i + 1) = c by omega] at this
        exact this.symm
      rw [e] at hv
      have e2 : liftN 1 c (Term.var i) = Term.var i := by simp [liftN, hlt]
      rw [e2]; exact hv
    · have hv := Rule.var (ctxIns c B Γ) (i + 1) A
        (by rw [ctxIns_ge hc (by omega)]; exact hi)
      have e : liftN (i + 1 + 1) 0 A = liftN 1 c (liftN (i + 1) 0 A) :=
        (Term.liftN_liftN_merge 1 (i + 1) A (Nat.zero_le _) (by omega)).symm
      rw [e] at hv
      have e2 : liftN 1 c (Term.var i) = Term.var (i + 1) := by simp [liftN, hlt]
      rw [e2]; exact hv
  | piType Γ A B' =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A type).wk c B, (typing (A :: Γ) B' type).wk (c + 1) B],
      Rule.piType _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, c, hc, rfl⟩
    · exact ⟨typing (A :: Γ) B' type, by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | piKind Γ A B' =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A type).wk c B, (typing (A :: Γ) B' kind).wk (c + 1) B],
      Rule.piKind _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, c, hc, rfl⟩
    · exact ⟨typing (A :: Γ) B' kind, by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | lamI Γ A B' t =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A type).wk c B, (typing (A :: Γ) t B').wk (c + 1) B],
      Rule.lamI _ _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, c, hc, rfl⟩
    · exact ⟨typing (A :: Γ) t B', by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | appE Γ A B' f a =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ f (Pi A B')).wk c B, (typing Γ a A).wk c B], ?_, ?_⟩
    · have := Rule.appE (ctxIns c B Γ) (liftN 1 c A) (liftN 1 (c + 1) B') (liftN 1 c f) (liftN 1 c a)
      rw [← show liftN 1 c (inst 0 a B') = inst 0 (liftN 1 c a) (liftN 1 (c + 1) B') by
        simpa using Term.liftN_inst 1 a B' (Nat.zero_le c)] at this
      exact this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ f (Pi A B'), by simp, c, hc, rfl⟩
      · exact ⟨typing Γ a A, by simp, c, hc, rfl⟩
  | conv Γ t A B' U =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ t A).wk c B, (equal Γ A B' U).wk c B], Rule.conv _ _ _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ t A, by simp, c, hc, rfl⟩
    · exact ⟨equal Γ A B' U, by simp, c, hc, rfl⟩
  | refl Γ t A =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ t A).wk c B], Rule.refl _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨typing Γ t A, by simp, c, hc, rfl⟩
  | symm Γ t u A =>
    simp only [ctx] at hc
    refine ⟨[(equal Γ t u A).wk c B], Rule.symm _ _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨equal Γ t u A, by simp, c, hc, rfl⟩
  | trans Γ t u v A =>
    simp only [ctx] at hc
    refine ⟨[(equal Γ t u A).wk c B, (equal Γ u v A).wk c B], Rule.trans _ _ _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨equal Γ t u A, by simp, c, hc, rfl⟩
    · exact ⟨equal Γ u v A, by simp, c, hc, rfl⟩
  | piCong Γ A A' B' B'' U =>
    simp only [ctx] at hc
    have e : liftN 1 (c + 1) (liftN 1 0 U) = liftN 1 0 (liftN 1 c U) :=
      Term.liftN_liftN_comm 1 1 U (c := c) (d := 0) (Nat.zero_le _)
    refine ⟨[(equal Γ A A' type).wk c B, (equal (A :: Γ) B' B'' (liftN 1 0 U)).wk (c + 1) B], ?_, ?_⟩
    · have := Rule.piCong (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c A') (liftN 1 (c + 1) B')
        (liftN 1 (c + 1) B'') (liftN 1 c U)
      simpa [Judgment.wk, ctxIns, liftN, e] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ A A' type, by simp, c, hc, rfl⟩
      · exact ⟨equal (A :: Γ) B' B'' (liftN 1 0 U), by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | lamCong Γ A A' B' t t' =>
    simp only [ctx] at hc
    refine ⟨[(equal Γ A A' type).wk c B, (equal (A :: Γ) t t' B').wk (c + 1) B],
      Rule.lamCong _ _ _ _ _ _, ?_⟩
    simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨equal Γ A A' type, by simp, c, hc, rfl⟩
    · exact ⟨equal (A :: Γ) t t' B', by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | appCong Γ A B' f f' a a' =>
    simp only [ctx] at hc
    refine ⟨[(equal Γ f f' (Pi A B')).wk c B, (equal Γ a a' A).wk c B], ?_, ?_⟩
    · have := Rule.appCong (ctxIns c B Γ) (liftN 1 c A) (liftN 1 (c + 1) B') (liftN 1 c f)
        (liftN 1 c f') (liftN 1 c a) (liftN 1 c a')
      rw [← show liftN 1 c (inst 0 a B') = inst 0 (liftN 1 c a) (liftN 1 (c + 1) B') by
        simpa using Term.liftN_inst 1 a B' (Nat.zero_le c)] at this
      exact this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ f f' (Pi A B'), by simp, c, hc, rfl⟩
      · exact ⟨equal Γ a a' A, by simp, c, hc, rfl⟩
  | beta Γ A B' t a =>
    simp only [ctx] at hc
    refine ⟨[(typing (A :: Γ) t B').wk (c + 1) B, (typing Γ a A).wk c B], ?_, ?_⟩
    · have := Rule.beta (ctxIns c B Γ) (liftN 1 c A) (liftN 1 (c + 1) B') (liftN 1 (c + 1) t)
        (liftN 1 c a)
      rw [← show liftN 1 c (inst 0 a B') = inst 0 (liftN 1 c a) (liftN 1 (c + 1) B') by
          simpa using Term.liftN_inst 1 a B' (Nat.zero_le c),
        ← show liftN 1 c (inst 0 a t) = inst 0 (liftN 1 c a) (liftN 1 (c + 1) t) by
          simpa using Term.liftN_inst 1 a t (Nat.zero_le c)] at this
      exact this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing (A :: Γ) t B', by simp, c + 1, by simpa [ctx] using hc, rfl⟩
      · exact ⟨typing Γ a A, by simp, c, hc, rfl⟩
  | eta Γ A B' f =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ f (Pi A B')).wk c B], ?_, ?_⟩
    · have := Rule.eta (ctxIns c B Γ) (liftN 1 c A) (liftN 1 (c + 1) B') (liftN 1 c f)
      have e : liftN 1 (c + 1) (liftN 1 0 f) = liftN 1 0 (liftN 1 c f) :=
        Term.liftN_liftN_comm 1 1 f (c := c) (d := 0) (Nat.zero_le _)
      simpa [Judgment.wk, liftN, e] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' rfl; exact ⟨typing Γ f (Pi A B'), by simp, c, hc, rfl⟩


theorem weakening : foundation.Weakening := fun hr _ hc B => Rule.wk hr hc B

/-- **Weakening is admissible in LF**: a variable can be inserted at any position of the
context, provided the signature's declarations are closed. -/
theorem weaken {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {J : Judgment} (h : Derivable foundation S J) :
    ∀ (c : Nat) (B : Term), c ≤ J.ctx.length → Derivable foundation S (J.wk c B) :=
  Derivable.weaken weakening hS h

/-- **Every LF rule is stable under substitution**, except the variable rule at the
substituted variable, which yields the substituted term itself. -/
theorem Rule.sub {ps : List Judgment} {j : Judgment} (h : Rule ps j) (d : Nat) (u : Term) :
    (∃ ps', Rule ps' (j.sub d u) ∧ SubPrem ps ps' j d u) ∨
    (∃ A, j.ctx[d]? = some A ∧ j.sub d u = typing (ctxSub d u j.ctx) (liftN d 0 u) (liftN d 0 A)) := by
  cases h with
  | univ Γ => exact .inl ⟨[], Rule.univ _, by simp [SubPrem]⟩
  | var Γ i A hi =>
    rcases Nat.lt_trichotomy i d with hlt | rfl | hgt
    · refine .inl ⟨[], ?_, by simp [SubPrem]⟩
      have hv := Rule.var (ctxSub d u Γ) i _ (ctxSub_lt hlt hi)
      have e : liftN (i + 1) 0 (inst (d - 1 - i) u A) = inst d u (liftN (i + 1) 0 A) := by
        have := Term.inst_liftN_low (i + 1) u A (c := 0) (j := d - 1 - i) (Nat.zero_le _)
        rw [show d - 1 - i + (i + 1) = d by omega] at this
        exact this.symm
      rw [e] at hv
      have e2 : inst d u (Term.var i) = Term.var i := by simp [inst, hlt]
      show Rule [] (typing (ctxSub d u Γ) (inst d u (.var i)) (inst d u (liftN (i + 1) 0 A)))
      rw [e2]; exact hv
    · refine .inr ⟨A, hi, ?_⟩
      show typing (ctxSub i u Γ) (inst i u (.var i)) (inst i u (liftN (i + 1) 0 A)) = _
      rw [Term.inst_liftN_skip u A (Nat.zero_le i) (by omega)]
      simp [inst, ctx]
    · refine .inl ⟨[], ?_, by simp [SubPrem]⟩
      have hv := Rule.var (ctxSub d u Γ) (i - 1) A (by rw [ctxSub_gt hgt]; exact hi)
      rw [show i - 1 + 1 = i by omega] at hv
      have e : inst d u (liftN (i + 1) 0 A) = liftN i 0 A :=
        Term.inst_liftN_skip u A (Nat.zero_le d) (by omega)
      have e2 : inst d u (Term.var i) = Term.var (i - 1) := by
        have h1 : ¬ i < d := by omega
        have h2 : ¬ i = d := by omega
        simp [inst, h1, h2]
      show Rule [] (typing (ctxSub d u Γ) (inst d u (.var i)) (inst d u (liftN (i + 1) 0 A)))
      rw [e, e2]; exact hv
  | piType Γ A B =>
    refine .inl ⟨[(typing Γ A type).sub d u, (typing (A :: Γ) B type).sub (d + 1) u],
      Rule.piType _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨typing (A :: Γ) B type, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | piKind Γ A B =>
    refine .inl ⟨[(typing Γ A type).sub d u, (typing (A :: Γ) B kind).sub (d + 1) u],
      Rule.piKind _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨typing (A :: Γ) B kind, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | lamI Γ A B t =>
    refine .inl ⟨[(typing Γ A type).sub d u, (typing (A :: Γ) t B).sub (d + 1) u],
      Rule.lamI _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ A type, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨typing (A :: Γ) t B, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | appE Γ A B f a =>
    refine .inl ⟨[(typing Γ f (Pi A B)).sub d u, (typing Γ a A).sub d u], ?_, ?_⟩
    · have := Rule.appE (ctxSub d u Γ) (inst d u A) (inst (d + 1) u B) (inst d u f) (inst d u a)
      rw [← show inst d u (inst 0 a B) = inst 0 (inst d u a) (inst (d + 1) u B) by
        simpa using Term.inst_inst u a B (Nat.zero_le d)] at this
      exact this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ f (Pi A B), by simp, d, rfl, rfl, rfl⟩
      · exact ⟨typing Γ a A, by simp, d, rfl, rfl, rfl⟩
  | conv Γ t A B U =>
    refine .inl ⟨[(typing Γ t A).sub d u, (equal Γ A B U).sub d u], Rule.conv _ _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨typing Γ t A, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨equal Γ A B U, by simp, d, rfl, rfl, rfl⟩
  | refl Γ t A =>
    refine .inl ⟨[(typing Γ t A).sub d u], Rule.refl _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨typing Γ t A, by simp, d, rfl, rfl, rfl⟩
  | symm Γ t t' A =>
    refine .inl ⟨[(equal Γ t t' A).sub d u], Rule.symm _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨equal Γ t t' A, by simp, d, rfl, rfl, rfl⟩
  | trans Γ t t' v A =>
    refine .inl ⟨[(equal Γ t t' A).sub d u, (equal Γ t' v A).sub d u], Rule.trans _ _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨equal Γ t t' A, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨equal Γ t' v A, by simp, d, rfl, rfl, rfl⟩
  | piCong Γ A A' B B' U =>
    have e : inst (d + 1) u (liftN 1 0 U) = liftN 1 0 (inst d u U) := by
      simpa using Term.inst_liftN_low 1 u U (c := 0) (j := d) (Nat.zero_le _)
    refine .inl ⟨[(equal Γ A A' type).sub d u, (equal (A :: Γ) B B' (liftN 1 0 U)).sub (d + 1) u],
      ?_, ?_⟩
    · have := Rule.piCong (ctxSub d u Γ) (inst d u A) (inst d u A') (inst (d + 1) u B)
        (inst (d + 1) u B') (inst d u U)
      simpa [Judgment.sub, ctxSub, inst, e] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ A A' type, by simp, d, rfl, rfl, rfl⟩
      · exact ⟨equal (A :: Γ) B B' (liftN 1 0 U), by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | lamCong Γ A A' B t t' =>
    refine .inl ⟨[(equal Γ A A' type).sub d u, (equal (A :: Γ) t t' B).sub (d + 1) u],
      Rule.lamCong _ _ _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨equal Γ A A' type, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨equal (A :: Γ) t t' B, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | appCong Γ A B f f' a a' =>
    refine .inl ⟨[(equal Γ f f' (Pi A B)).sub d u, (equal Γ a a' A).sub d u], ?_, ?_⟩
    · have := Rule.appCong (ctxSub d u Γ) (inst d u A) (inst (d + 1) u B) (inst d u f)
        (inst d u f') (inst d u a) (inst d u a')
      rw [← show inst d u (inst 0 a B) = inst 0 (inst d u a) (inst (d + 1) u B) by
        simpa using Term.inst_inst u a B (Nat.zero_le d)] at this
      exact this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ f f' (Pi A B), by simp, d, rfl, rfl, rfl⟩
      · exact ⟨equal Γ a a' A, by simp, d, rfl, rfl, rfl⟩
  | beta Γ A B t a =>
    refine .inl ⟨[(typing (A :: Γ) t B).sub (d + 1) u, (typing Γ a A).sub d u], ?_, ?_⟩
    · have := Rule.beta (ctxSub d u Γ) (inst d u A) (inst (d + 1) u B) (inst (d + 1) u t)
        (inst d u a)
      rw [← show inst d u (inst 0 a B) = inst 0 (inst d u a) (inst (d + 1) u B) by
          simpa using Term.inst_inst u a B (Nat.zero_le d),
        ← show inst d u (inst 0 a t) = inst 0 (inst d u a) (inst (d + 1) u t) by
          simpa using Term.inst_inst u a t (Nat.zero_le d)] at this
      exact this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing (A :: Γ) t B, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
      · exact ⟨typing Γ a A, by simp, d, rfl, rfl, rfl⟩
  | eta Γ A B f =>
    refine .inl ⟨[(typing Γ f (Pi A B)).sub d u], ?_, ?_⟩
    · have := Rule.eta (ctxSub d u Γ) (inst d u A) (inst (d + 1) u B) (inst d u f)
      have e : inst (d + 1) u (liftN 1 0 f) = liftN 1 0 (inst d u f) := by
        simpa using Term.inst_liftN_low 1 u f (c := 0) (j := d) (Nat.zero_le _)
      simpa [Judgment.sub, inst, e] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' rfl; exact ⟨typing Γ f (Pi A B), by simp, d, rfl, rfl, rfl⟩


theorem substitution : foundation.Substitution := fun hr d u => Rule.sub hr d u

/-- Weakening by a whole prefix. -/
theorem weaken_front {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {Γ₀ : Ctx} {u A : Term} (hu : Derivable foundation S (typing Γ₀ u A)) (Δ : Ctx) :
    Derivable foundation S (typing (Δ ++ Γ₀) (liftN Δ.length 0 u) (liftN Δ.length 0 A)) :=
  Derivable.weaken_front weakening hS hu Δ

/-- **The substitution lemma for LF**: if `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
`Δ[u/x], Γ ⊢ J[u/x]`. The signature's declarations must be closed. -/
theorem subst {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {u : Term} {J : Judgment} (h : Derivable foundation S J) (d : Nat) (A : Term)
    (hd : J.ctx[d]? = some A) (hu : Derivable foundation S (typing (J.ctx.drop (d + 1)) u A)) :
    Derivable foundation S (J.sub d u) :=
  Derivable.subst weakening hS substitution h d A hd hu

/-! ## Scoping -/

/-- Every context entry only refers to the entries after it. -/
def CtxScoped : Ctx → Prop
  | [] => True
  | A :: Γ => A.ClosedAt Γ.length ∧ CtxScoped Γ

/-- All terms of a judgment only use variables of its context. -/
def _root_.MMT.Judgment.Scoped : Judgment → Prop
  | .typing Γ t A => t.ClosedAt Γ.length ∧ A.ClosedAt Γ.length
  | .equal Γ t u A => t.ClosedAt Γ.length ∧ u.ClosedAt Γ.length ∧ A.ClosedAt Γ.length

theorem Term.liftN_closedAt_shift {k : Nat} : ∀ {t : Term} {n c : Nat}, t.ClosedAt n → c ≤ n →
    (liftN k c t).ClosedAt (n + k)
  | .var i, n, c, h, hc => by
    simp only [ClosedAt] at h
    by_cases hi : i < c
    · simp only [liftN, hi, ↓reduceIte, ClosedAt]; omega
    · simp only [liftN, hi, ↓reduceIte, ClosedAt]; omega
  | .const _, _, _, _, _ => trivial
  | .app f a, n, c, h, hc => ⟨liftN_closedAt_shift h.1 hc, liftN_closedAt_shift h.2 hc⟩
  | .bind b A t, n, c, h, hc => by
    refine ⟨liftN_closedAt_shift h.1 hc, liftN_closedAt_shift h.2.1 hc, ?_⟩
    have := liftN_closedAt_shift (k := k) h.2.2 (by omega : c + 1 ≤ n + 1)
    simpa [Nat.add_right_comm] using this

theorem Term.inst_closedAt' {a : Term} : ∀ {B : Term} {j n : Nat}, B.ClosedAt (n + 1) → j ≤ n →
    a.ClosedAt (n - j) → (inst j a B).ClosedAt n
  | .var x, j, n, hB, hj, ha => by
    simp only [ClosedAt] at hB
    by_cases h1 : x < j
    · simp only [inst, h1, ↓reduceIte, ClosedAt]; omega
    · by_cases h2 : x = j
      · subst h2
        simp only [inst, Nat.lt_irrefl, ↓reduceIte]
        have := liftN_closedAt_shift (k := x) ha (Nat.zero_le _)
        rwa [show n - x + x = n by omega] at this
      · simp only [inst, h1, h2, ↓reduceIte, ClosedAt]; omega
  | .const _, _, _, _, _, _ => trivial
  | .app f x, j, n, hB, hj, ha => ⟨inst_closedAt' hB.1 hj ha, inst_closedAt' hB.2 hj ha⟩
  | .bind b A t, j, n, hB, hj, ha => by
    refine ⟨inst_closedAt' hB.1 hj ha, inst_closedAt' hB.2.1 hj ha, ?_⟩
    exact inst_closedAt' hB.2.2 (by omega) (by simpa using ha)

theorem Term.liftN_closedAt_unshift {k : Nat} : ∀ {t : Term} {n c : Nat},
    (liftN k c t).ClosedAt (n + k) → c ≤ n → t.ClosedAt n
  | .var i, n, c, h, hc => by
    by_cases hi : i < c
    · simp only [liftN, hi, ↓reduceIte, ClosedAt] at h; show i < n; omega
    · simp only [liftN, hi, ↓reduceIte, ClosedAt] at h; show i < n; omega
  | .const _, _, _, _, _ => trivial
  | .app f a, n, c, h, hc => ⟨liftN_closedAt_unshift h.1 hc, liftN_closedAt_unshift h.2 hc⟩
  | .bind b A t, n, c, h, hc => by
    refine ⟨liftN_closedAt_unshift h.1 hc, liftN_closedAt_unshift h.2.1 hc, ?_⟩
    exact liftN_closedAt_unshift (by simpa [Nat.add_right_comm] using h.2.2) (by omega)

theorem ctxScoped_get : ∀ {Γ : Ctx} {i : Nat} {A : Term}, CtxScoped Γ → Γ[i]? = some A →
    A.ClosedAt (Γ.length - i - 1)
  | [], _, _, _, h => by simp at h
  | B :: Γ, 0, A, hs, h => by simp at h; subst h; simpa using hs.1
  | B :: Γ, i + 1, A, hs, h => by
    simp only [List.getElem?_cons_succ] at h
    have := ctxScoped_get hs.2 h
    simpa [show Γ.length + 1 - (i + 1) - 1 = Γ.length - i - 1 by omega] using this

/-- **Scoping**: in a derivable LF judgment with a well-scoped context, all terms only use
variables of the context. The signature's declarations must be closed. -/
theorem scoping {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {J : Judgment} (h : Derivable foundation S J) : CtxScoped J.ctx → J.Scoped := by
  induction h with
  | @const Γ c A d hc =>
    intro _; exact ⟨trivial, (hS c A d hc).1.mono (Nat.zero_le _)⟩
  | @defn Γ c A d hc =>
    intro _
    exact ⟨trivial, ((hS c A (some d) hc).2 d rfl).mono (Nat.zero_le _),
      (hS c A (some d) hc).1.mono (Nat.zero_le _)⟩
  | rule hr _ ih =>
    intro hΓ
    have IH := fun p (hp : p ∈ _) (hc : CtxScoped p.ctx) => ih p hp hc
    cases hr with
    | univ Γ => exact ⟨trivial, trivial⟩
    | var Γ i A hi =>
      simp only [Judgment.ctx] at hΓ
      have hl : i < Γ.length := by
        rcases Nat.lt_or_ge i Γ.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hi; cases hi
      refine ⟨by show i < Γ.length; exact hl, ?_⟩
      have := Term.liftN_closedAt_shift (k := i + 1) (ctxScoped_get hΓ hi) (Nat.zero_le _)
      rwa [show Γ.length - i - 1 + (i + 1) = Γ.length by omega] at this
    | piType Γ A B =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ A type) (by simp) hΓ
      have h2 := IH (.typing (A :: Γ) B type) (by simp) (⟨h1.1, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨trivial, h1.1, by simpa using h2.1⟩, trivial⟩
    | piKind Γ A B =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ A type) (by simp) hΓ
      have h2 := IH (.typing (A :: Γ) B kind) (by simp) (⟨h1.1, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨trivial, h1.1, by simpa using h2.1⟩, trivial⟩
    | lamI Γ A B t =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ A type) (by simp) hΓ
      have h2 := IH (.typing (A :: Γ) t B) (by simp) (⟨h1.1, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨trivial, h1.1, by simpa using h2.1⟩, ⟨trivial, h1.1, by simpa using h2.2⟩⟩
    | appE Γ A B f a =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ f (Pi A B)) (by simp) hΓ
      have h2 := IH (.typing Γ a A) (by simp) hΓ
      exact ⟨⟨h1.1, h2.1⟩, Term.inst_closedAt' h1.2.2.2 (Nat.zero_le _) (by simpa using h2.1)⟩
    | conv Γ t A B U =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ t A) (by simp) hΓ
      have h2 := IH (.equal Γ A B U) (by simp) hΓ
      exact ⟨h1.1, h2.2.1⟩
    | refl Γ t A =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ t A) (by simp) hΓ
      exact ⟨h1.1, h1.1, h1.2⟩
    | symm Γ t u A =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.equal Γ t u A) (by simp) hΓ
      exact ⟨h1.2.1, h1.1, h1.2.2⟩
    | trans Γ t u v A =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.equal Γ t u A) (by simp) hΓ
      have h2 := IH (.equal Γ u v A) (by simp) hΓ
      exact ⟨h1.1, h2.2.1, h1.2.2⟩
    | piCong Γ A A' B B' U =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.equal Γ A A' type) (by simp) hΓ
      have h2 := IH (.equal (A :: Γ) B B' (liftN 1 0 U)) (by simp) (⟨h1.1, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨trivial, h1.1, by simpa using h2.1⟩, ⟨trivial, h1.2.1, by simpa using h2.2.1⟩,
        Term.liftN_closedAt_unshift (k := 1) (by simpa using h2.2.2) (Nat.zero_le _)⟩
    | lamCong Γ A A' B t t' =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.equal Γ A A' type) (by simp) hΓ
      have h2 := IH (.equal (A :: Γ) t t' B) (by simp) (⟨h1.1, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨trivial, h1.1, by simpa using h2.1⟩, ⟨trivial, h1.2.1, by simpa using h2.2.1⟩,
        ⟨trivial, h1.1, by simpa using h2.2.2⟩⟩
    | appCong Γ A B f f' a a' =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.equal Γ f f' (Pi A B)) (by simp) hΓ
      have h2 := IH (.equal Γ a a' A) (by simp) hΓ
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩,
        Term.inst_closedAt' h1.2.2.2.2 (Nat.zero_le _) (by simpa using h2.1)⟩
    | beta Γ A B t a =>
      simp only [Judgment.ctx] at hΓ
      have h2 := IH (.typing Γ a A) (by simp) hΓ
      have h1 := IH (.typing (A :: Γ) t B) (by simp) (⟨h2.2, hΓ⟩ : CtxScoped (A :: Γ))
      exact ⟨⟨⟨trivial, h2.2, by simpa using h1.1⟩, h2.1⟩,
        Term.inst_closedAt' (by simpa using h1.1) (Nat.zero_le _) (by simpa using h2.1),
        Term.inst_closedAt' (by simpa using h1.2) (Nat.zero_le _) (by simpa using h2.1)⟩
    | eta Γ A B f =>
      simp only [Judgment.ctx] at hΓ
      have h1 := IH (.typing Γ f (Pi A B)) (by simp) hΓ
      refine ⟨h1.1, ⟨trivial, h1.2.2.1, ?_, ?_⟩, h1.2⟩
      · have := Term.liftN_closedAt_shift (k := 1) h1.1 (Nat.zero_le _)
        simpa using this
      · show 0 < Γ.length + 1; omega

end LF

end MMT
