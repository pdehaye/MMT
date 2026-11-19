import MMTlib.Core.Judgment

/-!
# Structural rules: weakening and substitution

The foundation interface only asks for *outer* context extension (adding variables at
the far end of the context), which needs no reindexing. This file proves, for every
foundation whose rules are stable under inner weakening (`Foundation.Weakening`) and
substitution (`Foundation.Substitution`):

* `Derivable.weaken`: a variable of any type can be inserted at any position of the
  context, shifting the variables above it;
* `Derivable.subst`: the substitution lemma. If `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
  `Δ[u/x], Γ ⊢ J[u/x]`.

The signature's types and definitions must be closed, which is the case for MMT
theories. It also collects the de Bruijn identities for lifting and substitution
that these proofs, and others, need. LF and STLC instantiate the interface
(`LF.weaken`, `LF.subst`, `STLC.weaken`, `STLC.subst`).
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

/-- The context of a judgment. -/
def ctx : Judgment → Ctx
  | typing Γ _ _ => Γ
  | equal Γ _ _ _ => Γ

/-- Weakening of a judgment: insert `B` at position `c`. -/
def wk (c : Nat) (B : Term) : Judgment → Judgment
  | typing Γ t A => typing (ctxIns c B Γ) (liftN 1 c t) (liftN 1 c A)
  | equal Γ t u A => equal (ctxIns c B Γ) (liftN 1 c t) (liftN 1 c u) (liftN 1 c A)

end Judgment

/-- Weakened premises: each new premise is a weakening of an old one. -/
def WkPrem (ps ps' : List Judgment) (B : Term) : Prop :=
  ∀ p' ∈ ps', ∃ p ∈ ps, ∃ c', c' ≤ p.ctx.length ∧ p' = p.wk c' B

/-- A foundation is stable under weakening if inserting a variable into the conclusion
of a rule yields a rule whose premises are weakenings of the old ones. -/
def Foundation.Weakening (F : Foundation) : Prop :=
  ∀ {ps : List Judgment} {j : Judgment}, F.Rule ps j → ∀ {c : Nat}, c ≤ j.ctx.length →
    ∀ B : Term, ∃ ps', F.Rule ps' (j.wk c B) ∧ WkPrem ps ps' B

/-- The signature's types and definitions are closed. -/
def Sig.ClosedDecls (S : Sig) : Prop :=
  ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0

/-- **Weakening is admissible** in a foundation stable under weakening. -/
theorem Derivable.weaken {F : Foundation} (hF : F.Weakening) {S : Sig} (hS : S.ClosedDecls)
    {J : Judgment} (h : Derivable F S J) :
    ∀ (c : Nat) (B : Term), c ≤ J.ctx.length → Derivable F S (J.wk c B) := by
  induction h with
  | @const Γ c' A d hc =>
    intro c B _
    have := (hS c' A d hc).1
    simpa [Judgment.wk, liftN, liftN_closed this] using (Derivable.const (Γ := ctxIns c B Γ) hc)
  | @defn Γ c' A d hc =>
    intro c B _
    have h1 := (hS c' A (some d) hc).1
    have h2 := (hS c' A (some d) hc).2 d rfl
    simpa [Judgment.wk, liftN, liftN_closed h1, liftN_closed h2] using
      (Derivable.defn (Γ := ctxIns c B Γ) hc)
  | rule hr _ ih =>
    intro c B hc
    obtain ⟨ps', hr', hps'⟩ := hF hr hc B
    refine .rule hr' (fun p' hp' => ?_)
    obtain ⟨p, hp, c', hc', rfl⟩ := hps' p' hp'
    exact ih p hp c' B hc'

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

/-- Substituted premises: each comes from an old premise, at the position of the same
variable. -/
def SubPrem (ps ps' : List Judgment) (j : Judgment) (d : Nat) (u : Term) : Prop :=
  ∀ p' ∈ ps', ∃ p ∈ ps, ∃ d', p.ctx.drop (d' + 1) = j.ctx.drop (d + 1) ∧
    p.ctx[d']? = j.ctx[d]? ∧ p' = p.sub d' u

theorem subPrem_ext {Γ : Ctx} {A : Term} {d : Nat} :
    (A :: Γ).drop (d + 1 + 1) = Γ.drop (d + 1) ∧ (A :: Γ)[d + 1]? = Γ[d]? := by simp
/-- A foundation is stable under substitution if substituting into the conclusion of a
rule yields a rule whose premises are substitutions of the old ones, except for the
variable rule at the substituted variable, whose conclusion becomes the typing of the
substituted term itself. -/
def Foundation.Substitution (F : Foundation) : Prop :=
  ∀ {ps : List Judgment} {j : Judgment}, F.Rule ps j → ∀ (d : Nat) (u : Term),
    (∃ ps', F.Rule ps' (j.sub d u) ∧ SubPrem ps ps' j d u) ∨
    (∃ A, j.ctx[d]? = some A ∧
      j.sub d u = .typing (ctxSub d u j.ctx) (liftN d 0 u) (liftN d 0 A))

section
open Judgment
variable {F : Foundation} (hF : F.Weakening) {S : Sig} (hS : S.ClosedDecls)
include hF hS

/-- Weakening by a whole prefix. -/
theorem Derivable.weaken_front
    {Γ₀ : Ctx} {u A : Term} (hu : Derivable F S (typing Γ₀ u A)) :
    ∀ Δ : Ctx, Derivable F S (typing (Δ ++ Γ₀) (liftN Δ.length 0 u) (liftN Δ.length 0 A))
  | [] => by simpa [Term.liftN_zero'] using hu
  | B :: Δ => by
    have := Derivable.weaken hF hS (Derivable.weaken_front hu Δ) 0 B (Nat.zero_le _)
    simp only [Judgment.wk, ctxIns] at this
    rw [Term.liftN_liftN_merge 1 Δ.length u (Nat.le_refl 0) (by omega),
      Term.liftN_liftN_merge 1 Δ.length A (Nat.le_refl 0) (by omega)] at this
    simpa using this


/-- **The substitution lemma**: if `Δ, x:A, Γ ⊢ J` and `Γ ⊢ u : A`, then
`Δ[u/x], Γ ⊢ J[u/x]`. The signature's declarations must be closed. -/
theorem Derivable.subst (hF' : F.Substitution)
    {u : Term} {J : Judgment} (h : Derivable F S J) :
    ∀ (d : Nat) (A : Term), J.ctx[d]? = some A →
      Derivable F S (typing (J.ctx.drop (d + 1)) u A) →
      Derivable F S (J.sub d u) := by
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
    rcases hF' hr d u with ⟨ps', hr', hps'⟩ | ⟨A', hA', heq⟩
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
      have := Derivable.weaken_front hF hS hu Δ
      rw [hΔl] at this
      exact this


end

end MMT
