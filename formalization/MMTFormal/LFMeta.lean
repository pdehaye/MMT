import MMTFormal.LF

/-!
# Metatheory of LF: weakening

The foundation interface only asks for *outer* context extension (adding variables
at the far end of the context), which needs no reindexing. This file proves *inner*
weakening for LF: a variable of any type can be inserted at any position of the
context, shifting the variables above it. The signature's types and definitions
must be closed, which is the case for MMT theories.

Main result: `LF.weaken`.
-/

namespace MMT

open Term

/-! ## de Bruijn identities for lifting -/

theorem Term.liftN_liftN_comm (k j : Nat) (t : Term) :
    ∀ {c d : Nat}, d ≤ c → liftN k (c + j) (liftN j d t) = liftN j d (liftN k c t) := by
  induction t with
  | var i =>
    intro c d hdc
    by_cases h1 : i < d
    · have h2 : i < c := by omega
      have h3 : i < c + j := by omega
      simp [liftN, h1, h2, h3]
    · by_cases h2 : i < c
      · have h3 : i + j < c + j := by omega
        simp [liftN, h1, h2, h3]
      · have h3 : ¬ (i + j < c + j) := by omega
        have h4 : ¬ (i + k < d) := by omega
        simp only [liftN, h1, h2, h3, h4, ↓reduceIte]
        congr 1; omega
  | const => intro _ _ _; rfl
  | app f a ihf iha => intro c d h; simp [liftN, ihf h, iha h]
  | bind b A t ihb ihA iht =>
    intro c d h
    simp only [liftN]
    rw [ihb h, ihA h, show c + j + 1 = (c + 1) + j by omega, iht (by omega : d + 1 ≤ c + 1)]

theorem Term.liftN_liftN_merge (k j : Nat) (t : Term) :
    ∀ {c d : Nat}, d ≤ c → c ≤ d + j → liftN k c (liftN j d t) = liftN (j + k) d t := by
  induction t with
  | var i =>
    intro c d h1 h2
    by_cases hi : i < d
    · have : i < c := by omega
      simp [liftN, hi, this]
    · have : ¬ (i + j < c) := by omega
      simp only [liftN, hi, this, ↓reduceIte]
      congr 1; omega
  | const => intro _ _ _ _; rfl
  | app f a ihf iha => intro c d h1 h2; simp [liftN, ihf h1 h2, iha h1 h2]
  | bind b A t ihb ihA iht =>
    intro c d h1 h2
    simp only [liftN]
    rw [ihb h1 h2, ihA h1 h2, iht (by omega) (by omega)]

/-- Lifting commutes with substitution. -/
theorem Term.liftN_inst (k : Nat) (a t : Term) :
    ∀ {j c : Nat}, j ≤ c →
      liftN k c (inst j a t) = inst j (liftN k (c - j) a) (liftN k (c + 1) t) := by
  induction t with
  | var i =>
    intro j c hjc
    by_cases h1 : i < j
    · have h2 : i < c := by omega
      have h3 : i < c + 1 := by omega
      simp [inst, liftN, h1, h2, h3]
    · by_cases h2 : i = j
      · subst h2
        have h3 : i < c + 1 := by omega
        simp only [inst, Nat.lt_irrefl, ↓reduceIte, liftN, h3]
        have := liftN_liftN_comm k i a (c := c - i) (d := 0) (Nat.zero_le _)
        rw [show c - i + i = c by omega] at this
        exact this
      · by_cases h3 : i < c + 1
        · have h4 : i - 1 < c := by omega
          simp [inst, liftN, h1, h2, h3, h4]
        · have h4 : ¬ (i - 1 < c) := by omega
          have h5 : ¬ (i + k < j) := by omega
          have h6 : ¬ (i + k = j) := by omega
          simp only [inst, liftN, h1, h2, h3, h4, h5, h6, ↓reduceIte]
          congr 1; omega
  | const => intro _ _ _; rfl
  | app f x ihf ihx => intro j c h; simp [inst, liftN, ihf h, ihx h]
  | bind b A t ihb ihA iht =>
    intro j c h
    simp only [inst, liftN]
    rw [ihb h, ihA h, iht (by omega : j + 1 ≤ c + 1), show c + 1 - (j + 1) = c - j by omega]

/-! ## Inserting a variable into a context -/

/-- Insert `B` at position `c` (so that it becomes `var c`), lifting the entries in
front of it. -/
def ctxIns : Nat → Term → Ctx → Ctx
  | 0, B, Γ => B :: Γ
  | _ + 1, _, [] => []
  | c + 1, B, A :: Γ => liftN 1 c A :: ctxIns c B Γ

theorem ctxIns_lt : ∀ {c : Nat} {B : Term} {Γ : Ctx} {i : Nat} {A : Term},
    i < c → Γ[i]? = some A → (ctxIns c B Γ)[i]? = some (liftN 1 (c - 1 - i) A)
  | 0, _, _, _, _, h, _ => by omega
  | _ + 1, _, [], _, _, _, h => by simp at h
  | c + 1, B, A' :: Γ, 0, A, _, h => by
    simp at h; subst h; simp [ctxIns]
  | c + 1, B, A' :: Γ, i + 1, A, hi, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [ctxIns, List.getElem?_cons_succ]
    rw [ctxIns_lt (by omega) h]
    congr 2; omega

theorem ctxIns_ge : ∀ {c : Nat} {B : Term} {Γ : Ctx} {i : Nat},
    c ≤ Γ.length → c ≤ i → (ctxIns c B Γ)[i + 1]? = Γ[i]?
  | 0, _, _, _, _, _ => by simp [ctxIns]
  | _ + 1, _, [], _, h, _ => by simp at h
  | c + 1, B, A :: Γ, i + 1, hl, hi => by
    simp only [ctxIns, List.getElem?_cons_succ]
    exact ctxIns_ge (by simpa using hl) (by omega)
  | c + 1, B, A :: Γ, 0, _, hi => by omega

theorem ctxIns_length : ∀ {c : Nat} {B : Term} {Γ : Ctx}, c ≤ Γ.length →
    (ctxIns c B Γ).length = Γ.length + 1
  | 0, _, _, _ => by simp [ctxIns]
  | _ + 1, _, [], h => by simp at h
  | c + 1, B, A :: Γ, h => by simp [ctxIns, ctxIns_length (by simpa using h : c ≤ Γ.length)]

namespace Judgment

def ctx : Judgment → Ctx
  | typing Γ _ _ => Γ
  | equal Γ _ _ _ => Γ

/-- Weakening of a judgment: insert `B` at position `c`. -/
def wk (c : Nat) (B : Term) : Judgment → Judgment
  | typing Γ t A => typing (ctxIns c B Γ) (liftN 1 c t) (liftN 1 c A)
  | equal Γ t u A => equal (ctxIns c B Γ) (liftN 1 c t) (liftN 1 c u) (liftN 1 c A)

end Judgment

namespace LF

open Judgment

/-- Weakened premises: each new premise is a weakening of an old one. -/
def WkPrem (ps ps' : List Judgment) (B : Term) : Prop :=
  ∀ p' ∈ ps', ∃ p ∈ ps, ∃ c', c' ≤ p.ctx.length ∧ p' = p.wk c' B

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

/-- **Weakening is admissible in LF**: a variable can be inserted at any position of the
context, provided the signature's declarations are closed. -/
theorem weaken {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {J : Judgment} (h : Derivable foundation S J) :
    ∀ (c : Nat) (B : Term), c ≤ J.ctx.length → Derivable foundation S (J.wk c B) := by
  induction h with
  | @const Γ c' A d hc =>
    intro c B _
    have := (hS c' A d hc).1
    simpa [wk, liftN, liftN_closed this] using (Derivable.const (Γ := ctxIns c B Γ) hc)
  | @defn Γ c' A d hc =>
    intro c B _
    have h1 := (hS c' A (some d) hc).1
    have h2 := (hS c' A (some d) hc).2 d rfl
    simpa [wk, liftN, liftN_closed h1, liftN_closed h2] using
      (Derivable.defn (Γ := ctxIns c B Γ) hc)
  | rule hr _ ih =>
    intro c B hc
    obtain ⟨ps', hr', hps'⟩ := Rule.wk hr hc B
    refine .rule hr' (fun p' hp' => ?_)
    obtain ⟨p, hp, c', hc', rfl⟩ := hps' p' hp'
    exact ih p hp c' B hc'

end LF

end MMT
