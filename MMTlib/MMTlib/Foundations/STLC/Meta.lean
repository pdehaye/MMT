import MMTlib.Core.Structural
import MMTlib.Foundations.STLC.Basic

/-!
# Metatheory of STLC

The rules of the simply typed λ-calculus are stable under inner weakening and
substitution (`STLC.Rule.wk`, `STLC.Rule.sub`), so the generic results of
`MMTlib.Core.Structural` apply: `STLC.weaken` and the substitution lemma `STLC.subst`.
The same generic proof serves LF; this is MMT's foundation-independence at the level
of metatheory.

As STLC has no conversion rule, typing can be inverted syntactically
(`STLC.inv_app`, `STLC.inv_lam`). With the substitution lemma this gives
`STLC.beta_typed`: contracting a well-typed β-redex preserves its type.
-/

namespace MMT.STLC

open Term Judgment

/-! ## Function types under lifting and substitution -/

theorem arr_wk (c : Nat) (A B : Term) :
    liftN 1 c (arr A B) = arr (liftN 1 c A) (liftN 1 c B) := by
  simp only [arr, liftN]
  rw [Term.liftN_liftN_comm 1 1 B (c := c) (d := 0) (Nat.zero_le _)]

theorem lift0_wk (c : Nat) (B : Term) :
    liftN 1 (c + 1) (liftN 1 0 B) = liftN 1 0 (liftN 1 c B) :=
  Term.liftN_liftN_comm 1 1 B (c := c) (d := 0) (Nat.zero_le _)

theorem lift0_sub (d : Nat) (u B : Term) :
    inst (d + 1) u (liftN 1 0 B) = liftN 1 0 (inst d u B) := by
  simpa using Term.inst_liftN_low 1 u B (c := 0) (j := d) (Nat.zero_le _)

theorem arr_sub (d : Nat) (u A B : Term) :
    inst d u (arr A B) = arr (inst d u A) (inst d u B) := by
  simp only [arr, inst]
  rw [lift0_sub]

theorem liftN_tp (k c : Nat) : liftN k c tp = tp := rfl
theorem inst_tp (d : Nat) (u : Term) : inst d u tp = tp := rfl
theorem liftN_app (k c : Nat) (f a : Term) :
    liftN k c (.app f a) = .app (liftN k c f) (liftN k c a) := rfl
theorem inst_app (d : Nat) (u f a : Term) :
    inst d u (.app f a) = .app (inst d u f) (inst d u a) := rfl
theorem liftN_lam (k c : Nat) (A t : Term) :
    liftN k c (lam A t) = lam (liftN k c A) (liftN k (c + 1) t) := rfl
theorem inst_lam (d : Nat) (u A t : Term) :
    inst d u (lam A t) = lam (inst d u A) (inst (d + 1) u t) := rfl

/-- Instantiating a lifted term. -/
theorem inst_lift0 (u B : Term) : inst 0 u (liftN 1 0 B) = B := by
  rw [Term.inst_liftN_skip (k := 0) (c := 0) (j := 0) u B (Nat.le_refl 0) (Nat.le_refl 0),
    Term.liftN_zero']

theorem arr_inj {A B A' B' : Term} (h : arr A B = arr A' B') : A = A' ∧ B = B' := by
  simp only [arr, Term.bind.injEq, true_and] at h
  refine ⟨h.1, ?_⟩
  have := congrArg (inst 0 (.var 0)) h.2
  rwa [inst_lift0, inst_lift0] at this

/-! ## Weakening -/

/-- **Every STLC rule is stable under weakening.** -/
theorem Rule.wk {ps : List Judgment} {j : Judgment} (h : Rule ps j) {c : Nat}
    (hc : c ≤ j.ctx.length) (B : Term) :
    ∃ ps', Rule ps' (j.wk c B) ∧ WkPrem ps ps' B := by
  cases h with
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
  | arrF Γ A B' =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A tp).wk c B, (typing Γ B' tp).wk c B], ?_, ?_⟩
    · simpa [Judgment.wk, arr_wk, liftN_tp] using Rule.arrF (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B')
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, c, hc, rfl⟩
      · exact ⟨typing Γ B' tp, by simp, c, hc, rfl⟩
  | lamI Γ A B' t =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A tp).wk c B, (typing (A :: Γ) t (B'.liftN 1 0)).wk (c + 1) B], ?_, ?_⟩
    · have := Rule.lamI (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B') (liftN 1 (c + 1) t)
      simpa [Judgment.wk, ctxIns, arr_wk, lift0_wk, liftN_tp, liftN_lam, liftN_app] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, c, hc, rfl⟩
      · exact ⟨_, by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | appE Γ A B' f a =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ f (arr A B')).wk c B, (typing Γ a A).wk c B], ?_, ?_⟩
    · have := Rule.appE (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B') (liftN 1 c f) (liftN 1 c a)
      simpa [Judgment.wk, arr_wk, liftN_app] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ f (arr A B'), by simp, c, hc, rfl⟩
      · exact ⟨typing Γ a A, by simp, c, hc, rfl⟩
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
  | appCong Γ A B' f f' a a' =>
    simp only [ctx] at hc
    refine ⟨[(equal Γ f f' (arr A B')).wk c B, (equal Γ a a' A).wk c B], ?_, ?_⟩
    · have := Rule.appCong (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B') (liftN 1 c f)
        (liftN 1 c f') (liftN 1 c a) (liftN 1 c a')
      simpa [Judgment.wk, arr_wk, liftN_app] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ f f' (arr A B'), by simp, c, hc, rfl⟩
      · exact ⟨equal Γ a a' A, by simp, c, hc, rfl⟩
  | lamCong Γ A B' t t' =>
    simp only [ctx] at hc
    refine ⟨[(typing Γ A tp).wk c B, (equal (A :: Γ) t t' (B'.liftN 1 0)).wk (c + 1) B], ?_, ?_⟩
    · have := Rule.lamCong (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B') (liftN 1 (c + 1) t)
        (liftN 1 (c + 1) t')
      simpa [Judgment.wk, ctxIns, arr_wk, lift0_wk, liftN_tp, liftN_lam, liftN_app] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, c, hc, rfl⟩
      · exact ⟨_, by simp, c + 1, by simpa [ctx] using hc, rfl⟩
  | beta Γ A B' t a =>
    simp only [ctx] at hc
    refine ⟨[(typing (A :: Γ) t (B'.liftN 1 0)).wk (c + 1) B, (typing Γ a A).wk c B], ?_, ?_⟩
    · have := Rule.beta (ctxIns c B Γ) (liftN 1 c A) (liftN 1 c B') (liftN 1 (c + 1) t)
        (liftN 1 c a)
      rw [← show liftN 1 c (inst 0 a t) = inst 0 (liftN 1 c a) (liftN 1 (c + 1) t) by
          simpa using Term.liftN_inst 1 a t (Nat.zero_le c)] at this
      simpa [Judgment.wk, ctxIns, lift0_wk, liftN_lam, liftN_app] using this
    · simp only [WkPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨_, by simp, c + 1, by simpa [ctx] using hc, rfl⟩
      · exact ⟨typing Γ a A, by simp, c, hc, rfl⟩

theorem weakening : foundation.Weakening := fun hr _ hc B => Rule.wk hr hc B

/-- **Weakening is admissible in STLC.** -/
theorem weaken {S : Sig} (hS : S.ClosedDecls) {J : Judgment} (h : Derivable foundation S J)
    (c : Nat) (B : Term) (hc : c ≤ J.ctx.length) : Derivable foundation S (J.wk c B) :=
  Derivable.weaken weakening hS h c B hc

/-! ## Substitution -/

/-- **Every STLC rule is stable under substitution**, except the variable rule at the
substituted variable. -/
theorem Rule.sub {ps : List Judgment} {j : Judgment} (h : Rule ps j) (d : Nat) (u : Term) :
    (∃ ps', Rule ps' (j.sub d u) ∧ SubPrem ps ps' j d u) ∨
    (∃ A, j.ctx[d]? = some A ∧ j.sub d u = typing (ctxSub d u j.ctx) (liftN d 0 u) (liftN d 0 A)) := by
  cases h with
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
  | arrF Γ A B =>
    refine .inl ⟨[(typing Γ A tp).sub d u, (typing Γ B tp).sub d u], ?_, ?_⟩
    · simpa [Judgment.sub, arr_sub, inst_tp] using Rule.arrF (ctxSub d u Γ) (inst d u A) (inst d u B)
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, d, rfl, rfl, rfl⟩
      · exact ⟨typing Γ B tp, by simp, d, rfl, rfl, rfl⟩
  | lamI Γ A B t =>
    refine .inl ⟨[(typing Γ A tp).sub d u, (typing (A :: Γ) t (B.liftN 1 0)).sub (d + 1) u],
      ?_, ?_⟩
    · have := Rule.lamI (ctxSub d u Γ) (inst d u A) (inst d u B) (inst (d + 1) u t)
      simpa [Judgment.sub, ctxSub, arr_sub, lift0_sub, inst_tp, inst_lam, inst_app] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, d, rfl, rfl, rfl⟩
      · exact ⟨_, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | appE Γ A B f a =>
    refine .inl ⟨[(typing Γ f (arr A B)).sub d u, (typing Γ a A).sub d u], ?_, ?_⟩
    · have := Rule.appE (ctxSub d u Γ) (inst d u A) (inst d u B) (inst d u f) (inst d u a)
      simpa [Judgment.sub, arr_sub, inst_app] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ f (arr A B), by simp, d, rfl, rfl, rfl⟩
      · exact ⟨typing Γ a A, by simp, d, rfl, rfl, rfl⟩
  | refl Γ t A =>
    refine .inl ⟨[(typing Γ t A).sub d u], Rule.refl _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨typing Γ t A, by simp, d, rfl, rfl, rfl⟩
  | symm Γ t t' A =>
    refine .inl ⟨[(equal Γ t t' A).sub d u], Rule.symm _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' rfl; exact ⟨equal Γ t t' A, by simp, d, rfl, rfl, rfl⟩
  | trans Γ t t' t'' A =>
    refine .inl ⟨[(equal Γ t t' A).sub d u, (equal Γ t' t'' A).sub d u], Rule.trans _ _ _ _ _, ?_⟩
    simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
    rintro p' (rfl | rfl)
    · exact ⟨equal Γ t t' A, by simp, d, rfl, rfl, rfl⟩
    · exact ⟨equal Γ t' t'' A, by simp, d, rfl, rfl, rfl⟩
  | appCong Γ A B f f' a a' =>
    refine .inl ⟨[(equal Γ f f' (arr A B)).sub d u, (equal Γ a a' A).sub d u], ?_, ?_⟩
    · have := Rule.appCong (ctxSub d u Γ) (inst d u A) (inst d u B) (inst d u f) (inst d u f')
        (inst d u a) (inst d u a')
      simpa [Judgment.sub, arr_sub, inst_app] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨equal Γ f f' (arr A B), by simp, d, rfl, rfl, rfl⟩
      · exact ⟨equal Γ a a' A, by simp, d, rfl, rfl, rfl⟩
  | lamCong Γ A B t t' =>
    refine .inl ⟨[(typing Γ A tp).sub d u, (equal (A :: Γ) t t' (B.liftN 1 0)).sub (d + 1) u],
      ?_, ?_⟩
    · have := Rule.lamCong (ctxSub d u Γ) (inst d u A) (inst d u B) (inst (d + 1) u t)
        (inst (d + 1) u t')
      simpa [Judgment.sub, ctxSub, arr_sub, lift0_sub, inst_tp, inst_lam, inst_app] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨typing Γ A tp, by simp, d, rfl, rfl, rfl⟩
      · exact ⟨_, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
  | beta Γ A B t a =>
    refine .inl ⟨[(typing (A :: Γ) t (B.liftN 1 0)).sub (d + 1) u, (typing Γ a A).sub d u],
      ?_, ?_⟩
    · have := Rule.beta (ctxSub d u Γ) (inst d u A) (inst d u B) (inst (d + 1) u t) (inst d u a)
      rw [← show inst d u (inst 0 a t) = inst 0 (inst d u a) (inst (d + 1) u t) by
        simpa using Term.inst_inst u a t (Nat.zero_le d)] at this
      simpa [Judgment.sub, ctxSub, lift0_sub, inst_lam, inst_app] using this
    · simp only [SubPrem, List.mem_cons, List.not_mem_nil, or_false]
      rintro p' (rfl | rfl)
      · exact ⟨_, by simp, d + 1, subPrem_ext.1, subPrem_ext.2, rfl⟩
      · exact ⟨typing Γ a A, by simp, d, rfl, rfl, rfl⟩

theorem substitution : foundation.Substitution := fun hr d u => Rule.sub hr d u

/-- **The substitution lemma for STLC**: if `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
`Δ[u/x], Γ ⊢ J[u/x]`. -/
theorem subst {S : Sig} (hS : S.ClosedDecls) {u : Term} {J : Judgment}
    (h : Derivable foundation S J) (d : Nat) (A : Term) (hd : J.ctx[d]? = some A)
    (hu : Derivable foundation S (typing (J.ctx.drop (d + 1)) u A)) :
    Derivable foundation S (J.sub d u) :=
  Derivable.subst weakening hS substitution h d A hd hu

/-! ## Inversion and β-reduction -/

/-- Inversion for application. -/
theorem inv_app {S : Sig} {Γ : Ctx} {f a B : Term}
    (h : Derivable foundation S (typing Γ (.app f a) B)) :
    ∃ A, Derivable foundation S (typing Γ f (arr A B)) ∧
      Derivable foundation S (typing Γ a A) := by
  cases h with
  | rule hr hps =>
    cases hr with
    | appE _ A _ _ _ => exact ⟨A, hps _ (by simp), hps _ (by simp)⟩

/-- Inversion for λ-abstraction. -/
theorem inv_lam {S : Sig} {Γ : Ctx} {A t T : Term}
    (h : Derivable foundation S (typing Γ (lam A t) T)) :
    ∃ B, T = arr A B ∧ Derivable foundation S (typing (A :: Γ) t (B.liftN 1 0)) := by
  generalize hx : lam A t = x at h
  cases h with
  | const => cases hx
  | rule hr hps =>
    cases hr with
    | lamI _ _ B _ =>
      simp only [lam, Term.bind.injEq, true_and] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨B, rfl, hps _ (by simp)⟩
    | arrF => simp [lam, arr, lamN, arrN] at hx
    | var => cases hx
    | appE => cases hx

/-- **Subject reduction for β-redexes**: contracting a well-typed redex preserves its
type. -/
theorem beta_typed {S : Sig} (hS : S.ClosedDecls) {Γ : Ctx} {A t a B : Term}
    (h : Derivable foundation S (typing Γ (.app (lam A t) a) B)) :
    Derivable foundation S (typing Γ (inst 0 a t) B) := by
  obtain ⟨A₀, hf, ha⟩ := inv_app h
  obtain ⟨B₁, he, ht⟩ := inv_lam hf
  obtain ⟨rfl, rfl⟩ := arr_inj he
  have := subst hS ht 0 A₀ rfl (by simpa [Judgment.ctx] using ha)
  simpa [Judgment.sub, ctxSub, inst_lift0] using this

end MMT.STLC
