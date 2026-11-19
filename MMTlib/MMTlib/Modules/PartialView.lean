import MMTlib.Modules.Basic
import MMTlib.Modules.Pushout

/-!
# Partial views

MMT allows *partial* views, which need not assign every constant of the domain. A
partial morphism `σ` sends a constant either to a term or to "undefined". Translating a
term along it is defined exactly when every constant in the term is defined.

The judgments derivable over the whole domain are generally *not* preserved: a
derivation may pass through undefined constants. The right statement is that a
partial morphism is a total morphism out of its *domain of definition*
`S.restrict σ`. All judgments derivable there are preserved, and on terms built from
defined constants the partial translation agrees with this total morphism.

Main results:
* `Term.ptrans_eq_some_iff`: partial translation is defined iff the term only uses
  defined constants, and then it equals the total translation.
* `IsPartialMorphism.preserves` and `IsPartialMorphism.typing_ptrans`: judgment
  preservation on the domain of definition.
* `IsPartialMorphism.total_of_cover`: a partial morphism that is defined everywhere is
  a total morphism.
* `IsPartialMorphism.comp`: composition of partial morphisms.
* `View.toPartial`: module-level partial views. Their totalization is `View.toSubst`,
  and a well-typed total view is also a partial view.
-/

namespace MMT

/-- Partial action on constants: `none` means "undefined". -/
abbrev PSubst := GName → Option Term

namespace PSubst

/-- `c` is in the domain of definition. -/
def Defined (σ : PSubst) (c : GName) : Prop := (σ c).isSome = true

/-- The totalization: undefined constants are kept as they are. -/
def total (σ : PSubst) : Subst := fun c => (σ c).getD (.const c)

end PSubst

/-- Partial translation of terms. -/
def Term.ptrans (σ : PSubst) : Term → Option Term
  | .var i => some (.var i)
  | .const c => σ c
  | .app f a =>
    match f.ptrans σ, a.ptrans σ with
    | some f', some a' => some (.app f' a')
    | _, _ => none
  | .bind b A t =>
    match b.ptrans σ, A.ptrans σ, t.ptrans σ with
    | some b', some A', some t' => some (.bind b' A' t')
    | _, _, _ => none

theorem Term.ptrans_of_usesOnly {σ : PSubst} {t : Term} (h : t.UsesOnly σ.Defined) :
    t.ptrans σ = some (t.trans σ.total) := by
  induction t with
  | var => rfl
  | const c =>
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
    simp [ptrans, Term.trans, PSubst.total, hu]
  | app f a ihf iha => simp [ptrans, Term.trans, ihf h.1, iha h.2]
  | bind b A t ihb ihA iht => simp [ptrans, Term.trans, ihb h.1, ihA h.2.1, iht h.2.2]

theorem Term.usesOnly_of_ptrans {σ : PSubst} {t u : Term} (h : t.ptrans σ = some u) :
    t.UsesOnly σ.Defined := by
  induction t generalizing u with
  | var => trivial
  | const c => simp [ptrans] at h; simp [UsesOnly, PSubst.Defined, h]
  | app f a ihf iha =>
    simp only [ptrans] at h
    cases hf : f.ptrans σ <;> cases ha : a.ptrans σ <;> simp [hf, ha] at h
    exact ⟨ihf hf, iha ha⟩
  | bind b A t ihb ihA iht =>
    simp only [ptrans] at h
    cases hb : b.ptrans σ <;> cases hA : A.ptrans σ <;> cases ht : t.ptrans σ <;>
      simp [hb, hA, ht] at h
    exact ⟨ihb hb, ihA hA, iht ht⟩

/-- Partial translation is defined exactly on terms over the domain of definition, and
agrees with the totalization there. -/
theorem Term.ptrans_eq_some_iff {σ : PSubst} {t u : Term} :
    t.ptrans σ = some u ↔ t.UsesOnly σ.Defined ∧ u = t.trans σ.total := by
  constructor
  · intro h
    have hu := usesOnly_of_ptrans h
    rw [ptrans_of_usesOnly hu] at h
    exact ⟨hu, (Option.some.inj h).symm⟩
  · rintro ⟨h, rfl⟩; exact ptrans_of_usesOnly h

/-- The domain of definition: restriction of `S` to the defined constants. -/
def Sig.restrict (S : Sig) (σ : PSubst) : Sig := fun c => if (σ c).isSome then S c else none

theorem Sig.restrict_sub (S : Sig) (σ : PSubst) : (S.restrict σ).Sub S := by
  intro c i h; unfold Sig.restrict at h; split at h <;> simp_all

theorem Sig.restrict_defined {S : Sig} {σ : PSubst} {c : GName} {i : ConstInfo}
    (h : S.restrict σ c = some i) : σ.Defined c := by
  unfold Sig.restrict at h; unfold PSubst.Defined; split at h <;> simp_all

/-- A well-typed partial morphism: a total morphism out of its domain of definition. -/
def IsPartialMorphism (F : Foundation) (S T : Sig) (σ : PSubst) : Prop :=
  IsMorphism F (S.restrict σ) T σ.total

/-- Restricting the domain of a morphism. -/
theorem IsMorphism.restrictDom {F : Foundation} {S₀ S T : Sig} {σ : Subst}
    (hS : S₀.Sub S) (h : IsMorphism F S T σ) : IsMorphism F S₀ T σ where
  closed := h.closed
  fixMeta := h.fixMeta
  typed hc := h.typed (hS _ _ hc)
  defn hc := h.defn (hS _ _ hc)

namespace IsPartialMorphism

variable {F : Foundation} {S T U : Sig} {σ τ : PSubst}

/-- Judgment preservation on the domain of definition. -/
theorem preserves (h : IsPartialMorphism F S T σ) {J : Judgment}
    (hJ : Derivable F (S.restrict σ) J) : Derivable F T (J.trans σ.total) :=
  Derivable.trans h hJ

/-- Closed typing judgments over the domain of definition are mapped by the partial
translation, which is defined on them. -/
theorem typing_ptrans (h : IsPartialMorphism F S T σ) {t A t' A' : Term}
    (hJ : Derivable F (S.restrict σ) (.typing [] t A))
    (ht : t.ptrans σ = some t') (hA : A.ptrans σ = some A') :
    Derivable F T (.typing [] t' A') := by
  obtain ⟨-, rfl⟩ := Term.ptrans_eq_some_iff.mp ht
  obtain ⟨-, rfl⟩ := Term.ptrans_eq_some_iff.mp hA
  simpa [Judgment.trans] using h.preserves hJ

/-- A partial morphism defined on all constants of its domain is total. -/
theorem total_of_cover (h : IsPartialMorphism F S T σ) (hcov : ∀ c, S.Has c → σ.Defined c) :
    IsMorphism F S T σ.total := by
  have : S.restrict σ = S := by
    funext c
    unfold Sig.restrict
    split
    · rfl
    · rename_i hn
      cases hc : S c with
      | none => rfl
      | some i => exact absurd (hcov c (by simp [Sig.Has, hc])) hn
  rw [IsPartialMorphism, this] at h
  exact h

/-- Every total morphism is a partial morphism defined everywhere. -/
theorem of_total {σ : Subst} (h : IsMorphism F S T σ) :
    IsPartialMorphism F S T (fun c => some (σ c)) := by
  have : (S.restrict fun c => some (σ c)) = S := by funext c; simp [Sig.restrict]
  unfold IsPartialMorphism; rw [this]
  have : PSubst.total (fun c => some (σ c)) = σ := by funext c; rfl
  rw [this]; exact h

end IsPartialMorphism

/-! ## Composition -/

/-- Composition of partial morphisms: `c` is defined if `σ c` is and its image is
over the domain of definition of `τ`. -/
def PSubst.comp (σ τ : PSubst) : PSubst := fun c => (σ c).bind (·.ptrans τ)

theorem PSubst.comp_defined {σ τ : PSubst} {c : GName} (h : (σ.comp τ).Defined c) :
    σ.Defined c := by
  unfold Defined comp at *; cases hc : σ c <;> simp_all

theorem PSubst.comp_total {σ τ : PSubst} {c : GName} (h : (σ.comp τ).Defined c) :
    (σ.comp τ).total c = (σ.total c).trans τ.total := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  unfold comp at hu
  cases hc : σ c with
  | none => simp [hc] at hu
  | some s =>
    simp only [hc, Option.bind_some] at hu
    obtain ⟨-, rfl⟩ := Term.ptrans_eq_some_iff.mp hu
    simp [total, comp, hc, hu]

/-- **Partial morphisms compose.** Suppose `σ` maps its domain of definition into the
domain of definition of `τ`, and the domain of definition of `σ;τ` is closed, i.e. its
declarations only use constants on which `σ;τ` is defined. Then `σ;τ` is a partial
morphism. -/
theorem IsPartialMorphism.comp {F : Foundation} {S T U : Sig} {σ τ : PSubst}
    (hσ : IsMorphism F (S.restrict σ) (T.restrict τ) σ.total)
    (hτ : IsPartialMorphism F T U τ)
    (hcl : ∀ c i, S.restrict (σ.comp τ) c = some i →
      (∀ A, i.tp = some A → A.UsesOnly (σ.comp τ).Defined) ∧
      (∀ e, i.df = some e → e.UsesOnly (σ.comp τ).Defined)) :
    IsPartialMorphism F S U (σ.comp τ) := by
  -- the composite agrees with the composition of totalizations where it is defined
  have agree : ∀ x : Term, x.UsesOnly (σ.comp τ).Defined →
      x.trans (σ.comp τ).total = (x.trans σ.total).trans τ.total := by
    intro x hx
    rw [← Term.trans_comp]
    exact Term.trans_congr hx (fun c hc => PSubst.comp_total hc)
  -- the domain of definition of the composite lies in that of `σ`
  have hsub : (S.restrict (σ.comp τ)).Sub (S.restrict σ) := by
    intro c i h
    have hd := PSubst.comp_defined (Sig.restrict_defined h)
    unfold Sig.restrict at *
    split at h
    · simp only [PSubst.Defined] at hd; simp [hd, h]
    · cases h
  have hcomp := hσ.comp hτ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    unfold PSubst.total PSubst.comp
    cases hc : σ c with
    | none => trivial
    | some s =>
      simp only [Option.bind_some]
      cases hp : s.ptrans τ with
      | none => trivial
      | some u =>
        obtain ⟨-, rfl⟩ := Term.ptrans_eq_some_iff.mp hp
        have : s = σ.total c := by simp [PSubst.total, hc]
        subst this
        exact (hσ.closed c).trans hτ.closed
  · intro c hc
    have h1 : σ.total c = .const c := hσ.fixMeta c hc
    have h2 : τ.total c = .const c := hτ.fixMeta c hc
    unfold PSubst.total PSubst.comp at *
    cases hs : σ c with
    | none => rfl
    | some s =>
      rw [hs] at h1; simp only [Option.getD_some] at h1; subst h1
      simp only [Option.bind_some, Term.ptrans]
      cases ht : τ c with
      | none => rfl
      | some t => rw [ht] at h2; simpa using h2
  · intro c A d hc
    have hd := Sig.restrict_defined hc
    rw [PSubst.comp_total hd, agree A ((hcl c _ hc).1 A rfl)]
    have := hcomp.typed (hsub _ _ hc)
    simpa [Subst.comp, Term.trans_comp] using this
  · intro c A d hc
    have hd := Sig.restrict_defined hc
    rw [PSubst.comp_total hd, agree A ((hcl c _ hc).1 A rfl), agree d ((hcl c _ hc).2 d rfl)]
    have := hcomp.defn (hsub _ _ hc)
    simpa [Subst.comp, Term.trans_comp] using this

/-! ## Partial views in the module system -/

/-- A view read as a partial morphism: local constants of the domain without an
assignment are undefined; all other constants are kept. -/
def View.toPartial (v : View) : PSubst := fun c =>
  if c.thy = v.dom then v.assign.lookup c.name else some (.const c)

/-- The totalization of a partial view is the elaboration used for total views. -/
theorem View.toPartial_total (v : View) : v.toPartial.total = v.toSubst := by
  funext c
  unfold PSubst.total toPartial toSubst
  split
  · cases v.assign.lookup c.name <;> rfl
  · rfl

/-- A partial view is well-typed if it is a partial morphism between the flattenings. -/
def View.PartialWellTyped (F : Foundation) (L : Library) (v : View) : Prop :=
  IsPartialMorphism F (flat L v.dom) (flat L v.cod) v.toPartial

/-- Total views are in particular partial views. -/
theorem View.WellTyped.toPartial {F : Foundation} {L : Library} {v : View}
    (h : v.WellTyped F L) : v.PartialWellTyped F L := by
  unfold PartialWellTyped IsPartialMorphism
  rw [View.toPartial_total]
  exact h.restrictDom (Sig.restrict_sub _ _)

/-- A partial view preserves all judgments over the constants it assigns. -/
theorem View.PartialWellTyped.preserves {F : Foundation} {L : Library} {v : View}
    (h : v.PartialWellTyped F L) {J : Judgment}
    (hJ : Derivable F ((flat L v.dom).restrict v.toPartial) J) :
    Derivable F (flat L v.cod) (J.trans v.toSubst) := by
  rw [← View.toPartial_total]; exact IsPartialMorphism.preserves h hJ

end MMT
