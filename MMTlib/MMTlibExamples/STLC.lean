import MMTlib.Foundations.STLC.ToLF

/-!
# Example: natural numbers in STLC, read in LF
-/

namespace MMT

open Term Judgment STLC

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
