import MMTlib.Foundations.LF.Basic

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

/-! ## de Bruijn identities for substitution -/

/-- Substituting into a variable that a lift skipped over. -/
theorem Term.inst_liftN_skip {k c j : Nat} (v t : Term) (h1 : c ≤ j) (h2 : j ≤ c + k) :
    inst j v (liftN (k + 1) c t) = liftN k c t := by
  induction t generalizing c j with
  | var i =>
    by_cases hi : i < c
    · have : i < j := by omega
      simp [liftN, inst, hi, this]
    · have h3 : ¬ (i + (k + 1) < j) := by omega
      have h4 : ¬ (i + (k + 1) = j) := by omega
      simp only [liftN, hi, ↓reduceIte, inst, h3, h4]
      show Term.var (i + (k + 1) - 1) = Term.var (i + k)
      congr 1
  | const _ => rfl
  | app f a ihf iha => simp [liftN, inst, ihf h1 h2, iha h1 h2]
  | bind b A t ihb ihA iht =>
    simp [liftN, inst, ihb h1 h2, ihA h1 h2, iht (by omega : c + 1 ≤ j + 1) (by omega)]

/-- Substituting above a lift. -/
theorem Term.inst_liftN_low (m : Nat) (u t : Term) :
    ∀ {c j : Nat}, c ≤ j → inst (j + m) u (liftN m c t) = liftN m c (inst j u t) := by
  induction t with
  | var x =>
    intro c j hcj
    by_cases h1 : x < c
    · have h2 : x < j + m := by omega
      have h3 : x < j := by omega
      simp [liftN, inst, h1, h2, h3]
    · by_cases h2 : x < j
      · have h3 : x + m < j + m := by omega
        simp [liftN, inst, h1, h2, h3]
      · by_cases h3 : x = j
        · subst h3
          simp only [liftN, h1, ↓reduceIte, inst, Nat.lt_irrefl]
          rw [Term.liftN_liftN_merge m x u (Nat.zero_le c) (by omega), Nat.add_comm]
        · have h4 : ¬ (x + m < j + m) := by omega
          have h5 : ¬ (x + m = j + m) := by omega
          have h6 : ¬ (x - 1 < c) := by omega
          simp only [liftN, h1, ↓reduceIte, inst, h4, h5, h2, h3, h6]
          congr 1; omega
  | const => intro _ _ _; rfl
  | app f a ihf iha => intro c j h; simp [liftN, inst, ihf h, iha h]
  | bind b A t ihb ihA iht =>
    intro c j h
    simp only [liftN, inst]
    rw [ihb h, ihA h, show j + m + 1 = (j + 1) + m by omega, iht (by omega : c + 1 ≤ j + 1)]

/-- Substitutions commute. -/
theorem Term.inst_inst (u a t : Term) :
    ∀ {i j : Nat}, i ≤ j → inst j u (inst i a t) = inst i (inst (j - i) u a) (inst (j + 1) u t) := by
  induction t with
  | var x =>
    intro i j hij
    by_cases h1 : x < i
    · have h2 : x < j := by omega
      have h3 : x < j + 1 := by omega
      simp [inst, h1, h2, h3]
    · by_cases h2 : x = i
      · subst h2
        have h3 : x < j + 1 := by omega
        simp only [inst, Nat.lt_irrefl, ↓reduceIte, h3]
        have := Term.inst_liftN_low x u a (c := 0) (j := j - x) (Nat.zero_le _)
        rwa [show j - x + x = j by omega] at this
      · by_cases h3 : x < j + 1
        · have h4 : x - 1 < j := by omega
          simp [inst, h1, h2, h3, h4]
        · by_cases h4 : x = j + 1
          · subst h4
            have h5 : ¬ (j + 1 - 1 < j) := by omega
            simp only [inst, h1, h2, Nat.lt_irrefl, ↓reduceIte, h5]
            simp only [show j + 1 - 1 = j by omega, ↓reduceIte]
            exact (Term.inst_liftN_skip (k := j) (c := 0) (j := i) (inst (j - i) u a) u
              (Nat.zero_le i) (by omega)).symm
          · have h5 : ¬ (x - 1 < j) := by omega
            have h6 : ¬ (x - 1 = j) := by omega
            have h7 : ¬ (x - 1 < i) := by omega
            have h8 : ¬ (x - 1 = i) := by omega
            simp only [inst, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
  | const => intro _ _ _; rfl
  | app f x ihf ihx => intro i j h; simp [inst, ihf h, ihx h]
  | bind b A t ihb ihA iht =>
    intro i j h
    simp only [inst]
    rw [ihb h, ihA h, iht (by omega : i + 1 ≤ j + 1), show j + 1 - (i + 1) = j - i by omega]

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

/-! ## Substitution -/

theorem Term.liftN_zero' (c : Nat) (t : Term) : liftN 0 c t = t := by
  induction t generalizing c with
  | var i => by_cases h : i < c <;> simp [liftN, h]
  | const _ => rfl
  | app f a ihf iha => simp [liftN, ihf, iha]
  | bind b A t ihb ihA iht => simp [liftN, ihb, ihA, iht]

/-- Substitute `u` for the variable at position `d` of a context. -/
def ctxSub : Nat → Term → Ctx → Ctx
  | _, _, [] => []
  | 0, _, _ :: Γ => Γ
  | d + 1, u, A :: Γ => inst d u A :: ctxSub d u Γ

theorem ctxSub_lt : ∀ {d : Nat} {u : Term} {Γ : Ctx} {i : Nat} {A : Term},
    i < d → Γ[i]? = some A → (ctxSub d u Γ)[i]? = some (inst (d - 1 - i) u A)
  | 0, _, _, _, _, h, _ => by omega
  | _ + 1, _, [], _, _, _, h => by simp at h
  | d + 1, u, A' :: Γ, 0, A, _, h => by simp at h; subst h; simp [ctxSub]
  | d + 1, u, A' :: Γ, i + 1, A, hi, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [ctxSub, List.getElem?_cons_succ]
    rw [ctxSub_lt (by omega) h]
    congr 2; omega

theorem ctxSub_gt : ∀ {d : Nat} {u : Term} {Γ : Ctx} {i : Nat},
    d < i → (ctxSub d u Γ)[i - 1]? = Γ[i]?
  | _, _, [], i, _ => by simp [ctxSub]
  | 0, u, A :: Γ, i + 1, _ => by simp [ctxSub]
  | d + 1, u, A :: Γ, i + 1, h => by
    simp only [ctxSub, List.getElem?_cons_succ]
    have := ctxSub_gt (d := d) (u := u) (Γ := Γ) (i := i) (by omega)
    rw [show i + 1 - 1 = (i - 1) + 1 by omega, List.getElem?_cons_succ, this]
  | _, _, _ :: _, 0, h => by omega

theorem ctxSub_split : ∀ {d : Nat} {u : Term} {Γ : Ctx}, d < Γ.length →
    ∃ Δ, ctxSub d u Γ = Δ ++ Γ.drop (d + 1) ∧ Δ.length = d
  | _, _, [], h => by simp at h
  | 0, u, A :: Γ, _ => ⟨[], by simp [ctxSub], rfl⟩
  | d + 1, u, A :: Γ, h => by
    obtain ⟨Δ, h1, h2⟩ := ctxSub_split (d := d) (u := u) (Γ := Γ) (by simpa using h)
    exact ⟨inst d u A :: Δ, by simp [ctxSub, h1], by simp [h2]⟩

namespace Judgment

/-- Substitution of `u` for the variable at position `d`. -/
def sub (d : Nat) (u : Term) : Judgment → Judgment
  | typing Γ t A => typing (ctxSub d u Γ) (inst d u t) (inst d u A)
  | equal Γ t t' A => equal (ctxSub d u Γ) (inst d u t) (inst d u t') (inst d u A)

end Judgment

namespace LF

open Judgment

/-- Substituted premises: each comes from an old premise, at the position of the same
variable. -/
def SubPrem (ps ps' : List Judgment) (j : Judgment) (d : Nat) (u : Term) : Prop :=
  ∀ p' ∈ ps', ∃ p ∈ ps, ∃ d', p.ctx.drop (d' + 1) = j.ctx.drop (d + 1) ∧
    p.ctx[d']? = j.ctx[d]? ∧ p' = p.sub d' u

theorem subPrem_ext {Γ : Ctx} {A : Term} {d : Nat} :
    (A :: Γ).drop (d + 1 + 1) = Γ.drop (d + 1) ∧ (A :: Γ)[d + 1]? = Γ[d]? := by simp

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

/-- Weakening by a whole prefix. -/
theorem weaken_front {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {Γ₀ : Ctx} {u A : Term} (hu : Derivable foundation S (typing Γ₀ u A)) :
    ∀ Δ : Ctx, Derivable foundation S (typing (Δ ++ Γ₀) (liftN Δ.length 0 u) (liftN Δ.length 0 A))
  | [] => by simpa [Term.liftN_zero'] using hu
  | B :: Δ => by
    have := weaken hS (weaken_front hS hu Δ) 0 B (Nat.zero_le _)
    simp only [Judgment.wk, ctxIns] at this
    rw [Term.liftN_liftN_merge 1 Δ.length u (Nat.le_refl 0) (by omega),
      Term.liftN_liftN_merge 1 Δ.length A (Nat.le_refl 0) (by omega)] at this
    simpa using this

/-- **The substitution lemma for LF**: if `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
`Δ[u/x], Γ ⊢ J[u/x]`. The signature's declarations must be closed. -/
theorem subst {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {u : Term} {J : Judgment} (h : Derivable foundation S J) :
    ∀ (d : Nat) (A : Term), J.ctx[d]? = some A →
      Derivable foundation S (typing (J.ctx.drop (d + 1)) u A) →
      Derivable foundation S (J.sub d u) := by
  induction h with
  | @const Γ c' A' e hc =>
    intro d A _ _
    have := (hS c' A' e hc).1
    simpa [Judgment.sub, inst, inst_closed this] using
      (Derivable.const (Γ := ctxSub d u Γ) hc)
  | @defn Γ c' A' e hc =>
    intro d A _ _
    have h1 := (hS c' A' (some e) hc).1
    have h2 := (hS c' A' (some e) hc).2 e rfl
    simpa [Judgment.sub, inst, inst_closed h1, inst_closed h2] using
      (Derivable.defn (Γ := ctxSub d u Γ) hc)
  | @rule ps j hr _ ih =>
    intro d A hd hu
    rcases Rule.sub hr d u with ⟨ps', hr', hps'⟩ | ⟨A', hA', heq⟩
    · refine .rule hr' (fun p' hp' => ?_)
      obtain ⟨p, hp, d', hdrop, hget, rfl⟩ := hps' p' hp'
      exact ih p hp d' A (by rw [hget]; exact hd) (by rw [hdrop]; exact hu)
    · rw [hd] at hA'; cases hA'
      rw [heq]
      have hlen : d < j.ctx.length := by
        rcases Nat.lt_or_ge d j.ctx.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hd; cases hd
      obtain ⟨Δ, hΔ, hΔl⟩ := ctxSub_split (u := u) hlen
      rw [hΔ]
      have := weaken_front hS hu Δ
      rw [hΔl] at this
      exact this


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
