import MMTFormal.LFMeta

/-!
# A second foundation, and foundation morphisms

MMT's module system works for any foundation. This file adds a second one, the simply
typed λ-calculus (STLC), and relates foundations by *foundation morphisms*: a
translation of terms under which every rule of the source foundation becomes derivable
in the target. Such a morphism transports every derivation (`FMor.preserves`). This is
the formal counterpart of translating a logic along a morphism of meta-theories.

* `STLC.foundation`: STLC, with types `tp`, non-dependent function types and λ. Its
  rules are proved stable under translation and context extension.
* `stlcToLF`: the embedding of STLC into LF (`tp ↦ type`, `→ ↦ Π`, `λ ↦ λ`). Its
  formation rule for function types needs weakening in LF (`LF.weaken`).
* `STLC.Example`: a derivation in an STLC theory of natural numbers, transported to LF.
-/

namespace MMT

open Term Judgment

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

/-! ## The simply typed λ-calculus -/

namespace STLC

def thy : ThyName := "STLC"
def tpN  : GName := ⟨thy, "tp"⟩
def arrN : GName := ⟨thy, "arrow"⟩
def lamN : GName := ⟨thy, "lambda"⟩

abbrev tp : Term := .const tpN
/-- `A → B`, as a binder that ignores its variable. -/
abbrev arr (A B : Term) : Term := .bind (.const arrN) A (B.liftN 1 0)
abbrev lam (A t : Term) : Term := .bind (.const lamN) A t

/-- The rules of STLC. -/
inductive Rule : List Judgment → Judgment → Prop where
  | var (Γ i A) : Γ[i]? = some A → Rule [] (typing Γ (.var i) (A.liftN (i + 1) 0))
  | arrF (Γ A B) : Rule [typing Γ A tp, typing Γ B tp] (typing Γ (arr A B) tp)
  | lamI (Γ A B t) : Rule [typing Γ A tp, typing (A :: Γ) t (B.liftN 1 0)]
      (typing Γ (lam A t) (arr A B))
  | appE (Γ A B f a) : Rule [typing Γ f (arr A B), typing Γ a A] (typing Γ (.app f a) B)
  | refl (Γ t A) : Rule [typing Γ t A] (equal Γ t t A)
  | symm (Γ t u A) : Rule [equal Γ t u A] (equal Γ u t A)
  | trans (Γ t u v A) : Rule [equal Γ t u A, equal Γ u v A] (equal Γ t v A)
  | appCong (Γ A B f f' a a') : Rule [equal Γ f f' (arr A B), equal Γ a a' A]
      (equal Γ (.app f a) (.app f' a') B)
  | lamCong (Γ A B t t') : Rule [typing Γ A tp, equal (A :: Γ) t t' (B.liftN 1 0)]
      (equal Γ (lam A t) (lam A t') (arr A B))
  | beta (Γ A B t a) : Rule [typing (A :: Γ) t (B.liftN 1 0), typing Γ a A]
      (equal Γ (.app (lam A t) a) (inst 0 a t) B)

theorem Rule.stable_trans (σ : Subst) (hσ : σ.Closed) (hfix : ∀ c, c.thy = thy → σ c = .const c)
    {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.trans σ)) (j.trans σ) := by
  have ht : σ tpN = tp := hfix _ rfl
  have ha : σ arrN = .const arrN := hfix _ rfl
  have hl : σ lamN = .const lamN := hfix _ rfl
  cases h with
  | var Γ i A hi =>
    have := Rule.var (Γ.map (·.trans σ)) i (A.trans σ) (by simp [hi])
    simpa [Judgment.trans, Term.trans, Term.trans_liftN hσ] using this
  | arrF Γ A B =>
    simpa [Judgment.trans, Term.trans, ht, ha, Term.trans_liftN hσ] using
      Rule.arrF (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ)
  | lamI Γ A B t =>
    simpa [Judgment.trans, Term.trans, ht, ha, hl, Term.trans_liftN hσ] using
      Rule.lamI (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ)
  | appE Γ A B f a =>
    simpa [Judgment.trans, Term.trans, ha, Term.trans_liftN hσ] using
      Rule.appE (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (a.trans σ)
  | refl Γ t A => simpa [Judgment.trans] using Rule.refl (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ)
  | symm Γ t u A =>
    simpa [Judgment.trans] using Rule.symm (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (A.trans σ)
  | trans Γ t u v A =>
    simpa [Judgment.trans] using
      Rule.trans (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (v.trans σ) (A.trans σ)
  | appCong Γ A B f f' a a' =>
    simpa [Judgment.trans, Term.trans, ha, Term.trans_liftN hσ] using
      Rule.appCong (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (f.trans σ) (f'.trans σ)
        (a.trans σ) (a'.trans σ)
  | lamCong Γ A B t t' =>
    simpa [Judgment.trans, Term.trans, ht, ha, hl, Term.trans_liftN hσ] using
      Rule.lamCong (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ) (t'.trans σ)
  | beta Γ A B t a =>
    simpa [Judgment.trans, Term.trans, hl, Term.trans_liftN hσ, Term.trans_inst hσ] using
      Rule.beta (Γ.map (·.trans σ)) (A.trans σ) (B.trans σ) (t.trans σ) (a.trans σ)

theorem Rule.stable_extend (Δ : Ctx) {ps : List Judgment} {j : Judgment} (h : Rule ps j) :
    Rule (ps.map (Judgment.extend Δ)) (j.extend Δ) := by
  cases h with
  | var Γ i A hi =>
    have hlt : i < Γ.length := by
      rcases Nat.lt_or_ge i Γ.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hi
    exact Rule.var _ i A (by rw [List.getElem?_append_left hlt]; exact hi)
  | arrF => exact Rule.arrF _ _ _
  | lamI => exact Rule.lamI _ _ _ _
  | appE => exact Rule.appE _ _ _ _ _
  | refl => exact Rule.refl _ _ _
  | symm => exact Rule.symm _ _ _ _
  | trans => exact Rule.trans _ _ _ _ _
  | appCong => exact Rule.appCong _ _ _ _ _ _ _
  | lamCong => exact Rule.lamCong _ _ _ _ _
  | beta => exact Rule.beta _ _ _ _ _

/-- STLC as an MMT foundation. -/
def foundation : Foundation where
  metaSym c := c.thy = thy
  Rule := Rule
  stable_trans σ hσ hfix _ _ h := Rule.stable_trans σ hσ hfix h
  stable_extend Δ _ _ h := Rule.stable_extend Δ h

end STLC

/-! ## Embedding STLC into LF -/

/-- `tp ↦ type`, `→ ↦ Π`, `λ ↦ λ`. -/
def stlcToLFSubst : Subst := fun c =>
  if c = STLC.tpN then LF.type
  else if c = STLC.arrN then .const LF.piN
  else if c = STLC.lamN then .const LF.lamN
  else .const c

/-- Signatures whose declarations are closed (needed for weakening in LF). -/
def ClosedSig (S : Sig) : Prop :=
  ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0

theorem stlcToLF_closed : stlcToLFSubst.Closed := by
  intro c; unfold stlcToLFSubst; repeat' split
  all_goals trivial

theorem transSig_closed {S : Sig} (hS : ClosedSig S) : ClosedSig (S.transSig stlcToLFSubst) := by
  intro c A d h
  simp only [Sig.transSig, Option.map_eq_some_iff] at h
  obtain ⟨⟨tp, df⟩, hc, hi⟩ := h
  simp only [ConstInfo.mk.injEq, Option.map_eq_some_iff] at hi
  obtain ⟨⟨A', hA', rfl⟩, hd⟩ := hi
  subst hA'
  refine ⟨(hS c A' df hc).1.trans stlcToLF_closed, fun e he => ?_⟩
  subst he
  obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp hd
  exact ((hS c A' df hc).2 e' he').trans stlcToLF_closed

/-- **The embedding of STLC into LF is a foundation morphism.** -/
def stlcToLF : FMor STLC.foundation LF.foundation ClosedSig where
  φ := stlcToLFSubst
  closed := stlcToLF_closed
  fix c hc := by
    simp only [STLC.foundation] at hc
    unfold stlcToLFSubst
    have h1 : c ≠ STLC.tpN := fun h => hc (by rw [h]; rfl)
    have h2 : c ≠ STLC.arrN := fun h => hc (by rw [h]; rfl)
    have h3 : c ≠ STLC.lamN := fun h => hc (by rw [h]; rfl)
    simp [h1, h2, h3]
  rules S hS {ps j} h hps := by
    have hcl := transSig_closed hS
    have ht : stlcToLFSubst STLC.tpN = LF.type := rfl
    have ha : stlcToLFSubst STLC.arrN = .const LF.piN := rfl
    have hl : stlcToLFSubst STLC.lamN = .const LF.lamN := rfl
    have hlift := Term.trans_liftN stlcToLF_closed
    have hinst := Term.trans_inst stlcToLF_closed
    -- premises, translated
    have P : ∀ p ∈ ps, Derivable LF.foundation (S.transSig stlcToLFSubst) (p.trans stlcToLFSubst) :=
      hps
    have mem2 : ∀ {p q r : Judgment}, r ∈ [p, q] → r = p ∨ r = q := by
      intro p q r h; simpa using h
    cases h with
    | var Γ i A hi =>
      have := LF.Rule.var (Γ.map (·.trans stlcToLFSubst)) i (A.trans stlcToLFSubst) (by simp [hi])
      have h' : LF.Rule [] ((typing Γ (.var i) (A.liftN (i + 1) 0)).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans, hlift] using this
      exact .rule h' (by simp)
    | arrF Γ A B =>
      have hA := P (typing Γ A STLC.tp) (by simp)
      have hB := P (typing Γ B STLC.tp) (by simp)
      simp only [Judgment.trans, Term.trans, ht] at hA hB
      have hB' := LF.weaken hcl hB 0 (A.trans stlcToLFSubst) (Nat.zero_le _)
      simp only [Judgment.wk, ctxIns] at hB'
      have := LF.Rule.piType (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        ((B.trans stlcToLFSubst).liftN 1 0)
      have h' : LF.Rule [typing (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst) LF.type,
          typing (A.trans stlcToLFSubst :: Γ.map (·.trans stlcToLFSubst))
            ((B.trans stlcToLFSubst).liftN 1 0) LF.type]
          ((typing Γ (STLC.arr A B) STLC.tp).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans, ht, ha, hlift] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact hA
      · simpa [liftN] using hB'
    | lamI Γ A B t =>
      have hA := P (typing Γ A STLC.tp) (by simp)
      have ht' := P (typing (A :: Γ) t (B.liftN 1 0)) (by simp)
      simp only [Judgment.trans, Term.trans, ht, List.map_cons, hlift] at hA ht'
      have := LF.Rule.lamI (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        ((B.trans stlcToLFSubst).liftN 1 0) (t.trans stlcToLFSubst)
      have h' : LF.Rule [typing (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst) LF.type,
          typing (A.trans stlcToLFSubst :: Γ.map (·.trans stlcToLFSubst)) (t.trans stlcToLFSubst)
            ((B.trans stlcToLFSubst).liftN 1 0)]
          ((typing Γ (STLC.lam A t) (STLC.arr A B)).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans, ha, hl, hlift] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact hA
      · exact ht'
    | appE Γ A B f a =>
      have hf := P (typing Γ f (STLC.arr A B)) (by simp)
      have ha' := P (typing Γ a A) (by simp)
      simp only [Judgment.trans, Term.trans, ha, hlift] at hf ha'
      have := LF.Rule.appE (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        ((B.trans stlcToLFSubst).liftN 1 0) (f.trans stlcToLFSubst) (a.trans stlcToLFSubst)
      rw [Term.inst_liftN_skip _ _ (Nat.le_refl 0) (by omega), Term.liftN_zero'] at this
      have h' : LF.Rule [typing (Γ.map (·.trans stlcToLFSubst)) (f.trans stlcToLFSubst)
            (LF.Pi (A.trans stlcToLFSubst) ((B.trans stlcToLFSubst).liftN 1 0)),
          typing (Γ.map (·.trans stlcToLFSubst)) (a.trans stlcToLFSubst) (A.trans stlcToLFSubst)]
          ((typing Γ (.app f a) B).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact hf
      · exact ha'
    | refl Γ t A =>
      exact .rule (LF.Rule.refl _ _ _) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact P (typing Γ t A) (by simp))
    | symm Γ t u A =>
      exact .rule (LF.Rule.symm _ _ _ _) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact P (equal Γ t u A) (by simp))
    | trans Γ t u v A =>
      exact .rule (LF.Rule.trans _ _ _ _ _) (fun p hp => by
        rcases mem2 hp with rfl | rfl
        · exact P (equal Γ t u A) (by simp)
        · exact P (equal Γ u v A) (by simp))
    | appCong Γ A B f f' a a' =>
      have hf := P (equal Γ f f' (STLC.arr A B)) (by simp)
      have ha' := P (equal Γ a a' A) (by simp)
      simp only [Judgment.trans, Term.trans, ha, hlift] at hf ha'
      have := LF.Rule.appCong (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        ((B.trans stlcToLFSubst).liftN 1 0) (f.trans stlcToLFSubst) (f'.trans stlcToLFSubst)
        (a.trans stlcToLFSubst) (a'.trans stlcToLFSubst)
      rw [Term.inst_liftN_skip _ _ (Nat.le_refl 0) (by omega), Term.liftN_zero'] at this
      have h' : LF.Rule [equal (Γ.map (·.trans stlcToLFSubst)) (f.trans stlcToLFSubst)
            (f'.trans stlcToLFSubst)
            (LF.Pi (A.trans stlcToLFSubst) ((B.trans stlcToLFSubst).liftN 1 0)),
          equal (Γ.map (·.trans stlcToLFSubst)) (a.trans stlcToLFSubst) (a'.trans stlcToLFSubst)
            (A.trans stlcToLFSubst)]
          ((equal Γ (.app f a) (.app f' a') B).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact hf
      · exact ha'
    | lamCong Γ A B t t' =>
      have hA := P (typing Γ A STLC.tp) (by simp)
      have ht' := P (equal (A :: Γ) t t' (B.liftN 1 0)) (by simp)
      simp only [Judgment.trans, Term.trans, ht, List.map_cons, hlift] at hA ht'
      have hrefl := LF.Rule.refl (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst) LF.type
      have := LF.Rule.lamCong (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        (A.trans stlcToLFSubst) ((B.trans stlcToLFSubst).liftN 1 0) (t.trans stlcToLFSubst)
        (t'.trans stlcToLFSubst)
      have h' : LF.Rule [equal (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
            (A.trans stlcToLFSubst) LF.type,
          equal (A.trans stlcToLFSubst :: Γ.map (·.trans stlcToLFSubst)) (t.trans stlcToLFSubst)
            (t'.trans stlcToLFSubst) ((B.trans stlcToLFSubst).liftN 1 0)]
          ((equal Γ (STLC.lam A t) (STLC.lam A t') (STLC.arr A B)).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans, ha, hl, hlift] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact .rule hrefl (by simpa using hA)
      · exact ht'
    | beta Γ A B t a =>
      have ht' := P (typing (A :: Γ) t (B.liftN 1 0)) (by simp)
      have ha' := P (typing Γ a A) (by simp)
      simp only [Judgment.trans, List.map_cons, hlift] at ht' ha'
      have := LF.Rule.beta (Γ.map (·.trans stlcToLFSubst)) (A.trans stlcToLFSubst)
        ((B.trans stlcToLFSubst).liftN 1 0) (t.trans stlcToLFSubst) (a.trans stlcToLFSubst)
      rw [Term.inst_liftN_skip _ _ (Nat.le_refl 0) (by omega), Term.liftN_zero'] at this
      have h' : LF.Rule [typing (A.trans stlcToLFSubst :: Γ.map (·.trans stlcToLFSubst))
            (t.trans stlcToLFSubst) ((B.trans stlcToLFSubst).liftN 1 0),
          typing (Γ.map (·.trans stlcToLFSubst)) (a.trans stlcToLFSubst) (A.trans stlcToLFSubst)]
          ((equal Γ (.app (STLC.lam A t) a) (inst 0 a t) B).trans stlcToLFSubst) := by
        simpa [Judgment.trans, Term.trans, hl, hinst] using this
      refine .rule h' (fun p hp => ?_)
      rcases mem2 hp with rfl | rfl
      · exact ht'
      · exact ha'

/-! ## Example: natural numbers in STLC, read in LF -/

namespace STLC.Example

def gN : GName := ⟨"NatSTLC", "N"⟩
def gz : GName := ⟨"NatSTLC", "z"⟩
def gs : GName := ⟨"NatSTLC", "s"⟩

def N : Term := .const gN

/-- `N : tp`, `z : N`, `s : N → N`. -/
def natSig : Sig := fun c =>
  if c = gN then some ⟨some tp, none⟩
  else if c = gz then some ⟨some N, none⟩
  else if c = gs then some ⟨some (arr N N), none⟩
  else none

theorem r2 {S : Sig} {p q j} (h : STLC.Rule [p, q] j) (hp : Derivable foundation S p)
    (hq : Derivable foundation S q) : Derivable foundation S j :=
  .rule h (by simp; exact ⟨hp, hq⟩)

/-- `s (s z) : N` in STLC. -/
theorem ssz : Derivable foundation natSig (.typing [] (.app (.const gs) (.app (.const gs) (.const gz))) N) := by
  have hs : Derivable foundation natSig (.typing [] (.const gs) (arr N N)) :=
    .const (d := none) (by simp [natSig, gs, gN, gz])
  have hz : Derivable foundation natSig (.typing [] (.const gz) N) :=
    .const (d := none) (by simp [natSig, gN, gz])
  exact r2 (Rule.appE [] N N _ _) hs (r2 (Rule.appE [] N N _ _) hs hz)

theorem natSig_closed : ClosedSig natSig := by
  intro c A d h
  unfold natSig at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨by simp [N, liftN, ClosedAt], fun e he => by cases he⟩)
    | cases h

theorem natSig_not_meta : ∀ c i, natSig c = some i → ¬ foundation.metaSym c := by
  intro c i h
  simp only [foundation]
  unfold natSig at h
  repeat' split at h
  all_goals first | (subst_vars; decide) | cases h

/-- **The same derivation, read in LF** along the embedding: `s (s z) : N` where now
`s : Π _:N. N` and `N : type`. -/
theorem ssz_LF : Derivable LF.foundation (natSig.transSig stlcToLFSubst)
    (.typing [] (.app (.const gs) (.app (.const gs) (.const gz))) N) := by
  have := stlcToLF.preserves natSig_closed natSig_not_meta ssz
  simpa [Judgment.trans, Term.trans, stlcToLF, stlcToLFSubst, gs, gz, gN, N, STLC.tpN,
    STLC.arrN, STLC.lamN] using this

end STLC.Example

end MMT
