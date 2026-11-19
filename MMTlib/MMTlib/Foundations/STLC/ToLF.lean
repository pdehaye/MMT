import MMTlib.Core.FoundationMorphism
import MMTlib.Foundations.STLC.Basic
import MMTlib.Foundations.LF.Meta

/-!
# Embedding STLC into LF

The translation `tp ↦ type`, `→ ↦ Π`, `λ ↦ λ` is a foundation morphism from STLC to LF
(`stlcToLF`). The formation rule for function types is derived using weakening in LF
(`LF.weaken`), which needs closed signatures (`ClosedSig`).
-/

namespace MMT

open Term Judgment

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

end MMT
