import MMTlib.Foundations.LF.Meta

/-!
# Confluence of β-reduction

This file proves that untyped β-reduction on MMT terms, with LF's `λ` as the only
redex-forming binder, is confluent (the Church–Rosser theorem). The proof follows
Tait and Martin-Löf, in Takahashi's formulation: parallel reduction `Par` has the
triangle property with respect to the complete development `dev`, so it has the
diamond property, and its reflexive-transitive closure coincides with that of
one-step reduction.

β-reduction is the computational content of LF's `beta` rule. Confluence is the
first ingredient of decidability of LF's definitional equality (the other is
normalization of well-typed terms, which is not formalized here). It also gives
unique normal forms (`Red.normal_unique`) and characterizes β-conversion by common
reducts (`Conv.joinable`).

Main results: `LF.Par.diamond`, `LF.Red.confluent`, `LF.Conv.joinable`.
-/

namespace MMT.LF


/-! ## Reduction relations -/

/-- One-step β-reduction, closed under all term constructors. -/
inductive Step : Term → Term → Prop
  /-- Contracting a β-redex `(λ x:A. t) a ⟶ t[a/x]`. -/
  | beta (A t a : Term) : Step (.app (lam A t) a) (Term.inst 0 a t)
  /-- Reducing the function of an application. -/
  | appL {f f' : Term} (a : Term) : Step f f' → Step (.app f a) (.app f' a)
  /-- Reducing the argument of an application. -/
  | appR (f : Term) {a a' : Term} : Step a a' → Step (.app f a) (.app f a')
  /-- Reducing the binder of a binding. -/
  | bindB {b b' : Term} (A t : Term) : Step b b' → Step (.bind b A t) (.bind b' A t)
  /-- Reducing the type of the bound variable. -/
  | bindA (b : Term) {A A' : Term} (t : Term) : Step A A' → Step (.bind b A t) (.bind b A' t)
  /-- Reducing the body of a binding. -/
  | bindT (b A : Term) {t t' : Term} : Step t t' → Step (.bind b A t) (.bind b A t')

/-- The reflexive-transitive closure of a relation. -/
inductive Star (R : Term → Term → Prop) : Term → Term → Prop
  /-- Zero steps. -/
  | refl (t : Term) : Star R t t
  /-- One more step at the end. -/
  | tail {t u v : Term} : Star R t u → R u v → Star R t v

/-- Multi-step β-reduction. -/
abbrev Red : Term → Term → Prop := Star Step

/-- Parallel β-reduction: contracts any set of redexes present in the term, all at once. -/
inductive Par : Term → Term → Prop
  /-- Variables. -/
  | var (i : Nat) : Par (.var i) (.var i)
  /-- Constants. -/
  | const (c : GName) : Par (.const c) (.const c)
  /-- Applications, componentwise. -/
  | app {f f' a a' : Term} : Par f f' → Par a a' → Par (.app f a) (.app f' a')
  /-- Bindings, componentwise. -/
  | bind {b b' A A' t t' : Term} : Par b b' → Par A A' → Par t t' →
      Par (.bind b A t) (.bind b' A' t')
  /-- Contracting a redex after reducing its components. -/
  | beta {A t t' a a' : Term} : Par t t' → Par a a' → Par (.app (lam A t) a) (Term.inst 0 a' t')

/-! ## Reflexive-transitive closures -/

namespace Star

variable {R : Term → Term → Prop}

/-- A single step. -/
theorem single {t u : Term} (h : R t u) : Star R t u := .tail (.refl t) h

/-- Composition of reduction sequences. -/
theorem trans {t u v : Term} (h1 : Star R t u) (h2 : Star R u v) : Star R t v := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact .tail ih h

/-- Adding a step at the front. -/
theorem head {t u v : Term} (h1 : R t u) (h2 : Star R u v) : Star R t v :=
  trans (single h1) h2

/-- A relation-preserving map on terms preserves reduction sequences. -/
theorem map {S : Term → Term → Prop} (F : Term → Term) (hF : ∀ {t u}, R t u → S (F t) (F u))
    {t u : Term} (h : Star R t u) : Star S (F t) (F u) := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact .tail ih (hF h)

/-- Monotonicity in the relation, up to taking closures. -/
theorem flatten {S : Term → Term → Prop} (hRS : ∀ {t u}, R t u → Star S t u)
    {t u : Term} (h : Star R t u) : Star S t u := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact trans ih (hRS h)

end Star

/-! ## Congruence of multi-step reduction -/

namespace Red

theorem appL {f f' : Term} (a : Term) (h : Red f f') : Red (.app f a) (.app f' a) :=
  Star.map (fun f => .app f a) (Step.appL a) h

theorem appR (f : Term) {a a' : Term} (h : Red a a') : Red (.app f a) (.app f a') :=
  Star.map (fun a => .app f a) (Step.appR f) h

/-- Multi-step reduction is a congruence for application. -/
theorem app {f f' a a' : Term} (hf : Red f f') (ha : Red a a') : Red (.app f a) (.app f' a') :=
  Star.trans (appL a hf) (appR f' ha)

/-- Multi-step reduction is a congruence for binding. -/
theorem bind {b b' A A' t t' : Term} (hb : Red b b') (hA : Red A A') (ht : Red t t') :
    Red (.bind b A t) (.bind b' A' t') :=
  Star.trans (Star.map (fun b => .bind b A t) (Step.bindB A t) hb) <|
    Star.trans (Star.map (fun A => .bind b' A t) (Step.bindA b' t) hA)
      (Star.map (fun t => .bind b' A' t) (Step.bindT b' A') ht)

end Red

/-! ## Parallel reduction lies between one-step and multi-step reduction -/

namespace Par

/-- Parallel reduction is reflexive. -/
theorem rfl' : ∀ t : Term, Par t t
  | .var i => .var i
  | .const c => .const c
  | .app f a => .app (rfl' f) (rfl' a)
  | .bind b A t => .bind (rfl' b) (rfl' A) (rfl' t)

/-- Every step is a parallel step. -/
theorem of_step {t u : Term} (h : Step t u) : Par t u := by
  induction h with
  | beta A t a => exact .beta (rfl' t) (rfl' a)
  | appL a _ ih => exact .app ih (rfl' a)
  | appR f _ ih => exact .app (rfl' f) ih
  | bindB A t _ ih => exact .bind ih (rfl' A) (rfl' t)
  | bindA b t _ ih => exact .bind (rfl' b) ih (rfl' t)
  | bindT b A _ ih => exact .bind (rfl' b) (rfl' A) ih

/-- Every parallel step is a reduction sequence. -/
theorem toRed {t u : Term} (h : Par t u) : Red t u := by
  induction h with
  | var => exact .refl _
  | const => exact .refl _
  | app _ _ ihf iha => exact Red.app ihf iha
  | bind _ _ _ ihb ihA iht => exact Red.bind ihb ihA iht
  | @beta A t t' a a' _ _ iht iha =>
    exact Star.trans (Red.app (Red.bind (.refl _) (.refl A) iht) iha)
      (Star.single (Step.beta A t' a'))

/-- Parallel steps are stable under lifting. -/
theorem liftN {t t' : Term} (h : Par t t') (k : Nat) : ∀ c, Par (Term.liftN k c t) (Term.liftN k c t') := by
  induction h with
  | var i =>
    intro c; simp only [Term.liftN]; split <;> exact .var _
  | const => intro c; exact .const _
  | app _ _ ihf iha => intro c; exact .app (ihf c) (iha c)
  | bind _ _ _ ihb ihA iht => intro c; exact .bind (ihb c) (ihA c) (iht (c + 1))
  | @beta A t t' a a' _ _ iht iha =>
    intro c
    have e := Term.liftN_inst k a' t' (j := 0) (c := c) (Nat.zero_le c)
    rw [Nat.sub_zero] at e
    rw [e]
    exact .beta (iht (c + 1)) (iha c)

/-- Parallel steps are stable under substitution of parallel steps. -/
theorem inst {t t' : Term} (h : Par t t') {u u' : Term} (hu : Par u u') :
    ∀ j, Par (Term.inst j u t) (Term.inst j u' t') := by
  induction h with
  | var i =>
    intro j
    simp only [Term.inst]
    split
    · exact .var _
    · split
      · exact hu.liftN j 0
      · exact .var _
  | const => intro j; exact .const _
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | bind _ _ _ ihb ihA iht => intro j; exact .bind (ihb j) (ihA j) (iht (j + 1))
  | @beta A t t' a a' _ _ iht iha =>
    intro j
    have e := Term.inst_inst u' a' t' (i := 0) (j := j) (Nat.zero_le j)
    rw [Nat.sub_zero] at e
    rw [e]
    exact .beta (iht (j + 1)) (iha j)

end Par

/-! ## Complete development -/

/-- The complete development: contracts every redex of the term, innermost first. -/
def dev : Term → Term
  | .var i => .var i
  | .const c => .const c
  | .app (.bind (.const c) A t) a =>
      if c = lamN then Term.inst 0 (dev a) (dev t) else .app (.bind (.const c) (dev A) (dev t)) (dev a)
  | .app f a => .app (dev f) (dev a)
  | .bind b A t => .bind (dev b) (dev A) (dev t)

/-- Whether a term is a λ-abstraction. -/
def IsLam : Term → Prop
  | .bind (.const c) _ _ => c = lamN
  | _ => False

instance : DecidablePred IsLam := fun t => by
  unfold IsLam; split <;> infer_instance

theorem dev_app_lam (A t a : Term) : dev (.app (lam A t) a) = Term.inst 0 (dev a) (dev t) := by
  simp [dev]

theorem dev_app_of_not_lam {f : Term} (hf : ¬ IsLam f) (a : Term) :
    dev (.app f a) = .app (dev f) (dev a) := by
  match f with
  | .var _ => simp [dev]
  | .const _ => simp [dev]
  | .app _ _ => simp [dev]
  | .bind (.var _) _ _ => simp [dev]
  | .bind (.app _ _) _ _ => simp [dev]
  | .bind (.bind _ _ _) _ _ => simp [dev]
  | .bind (.const c) A t =>
    have : c ≠ lamN := hf
    simp [dev, this]

/-- Inversion for parallel steps from a λ-abstraction. -/
theorem Par.lam_inv {A t u : Term} (h : Par (lam A t) u) :
    ∃ A' t', u = lam A' t' ∧ Par A A' ∧ Par t t' := by
  cases h with
  | bind hb hA ht =>
    cases hb
    exact ⟨_, _, rfl, hA, ht⟩

/-- The triangle property: every parallel step can be completed to the complete development. -/
theorem Par.triangle {t u : Term} (h : Par t u) : Par u (dev t) := by
  induction h with
  | var i => exact .var i
  | const c => exact .const c
  | bind _ _ _ ihb ihA iht => exact .bind ihb ihA iht
  | @beta A t t' a a' _ _ iht iha =>
    rw [dev_app_lam]
    exact iht.inst iha 0
  | @app f f' a a' hf _ ihf iha =>
    by_cases hl : IsLam f
    · match f, hl with
      | .bind (.const c) A t, hl =>
        have hc : c = lamN := hl
        subst hc
        obtain ⟨A', t', rfl, _, _⟩ := hf.lam_inv
        rw [dev_app_lam]
        have ihf' : Par (lam A' t') (lam (dev A) (dev t)) := by simpa [dev] using ihf
        obtain ⟨_, _, he, _, ht'⟩ := ihf'.lam_inv
        cases he
        exact .beta ht' iha
    · rw [dev_app_of_not_lam hl]
      exact .app ihf iha

/-- The diamond property of parallel reduction. -/
theorem Par.diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨dev t, hu.triangle, hv.triangle⟩

/-! ## Confluence -/

/-- The strip lemma: a parallel step and a sequence of parallel steps can be joined. -/
theorem Par.strip {t u v : Term} (hu : Par t u) (hv : Star Par t v) :
    ∃ w, Star Par u w ∧ Par v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, .refl u, hu⟩
  | tail _ hvw ih =>
    obtain ⟨w, huw, hw⟩ := ih hu
    obtain ⟨x, hwx, hx⟩ := Par.diamond hw hvw
    exact ⟨x, .tail huw hwx, hx⟩

/-- Sequences of parallel steps are confluent. -/
theorem Par.confluent {t u v : Term} (hu : Star Par t u) (hv : Star Par t v) :
    ∃ w, Star Par u w ∧ Star Par v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, .refl v⟩
  | tail _ hab ih =>
    obtain ⟨w, haw, hvw⟩ := ih hv
    obtain ⟨x, hbx, hwx⟩ := Par.strip hab haw
    exact ⟨x, hbx, .tail hvw hwx⟩

theorem Red.toParStar {t u : Term} (h : Red t u) : Star Par t u :=
  Star.flatten (fun h => Star.single (Par.of_step h)) h

theorem Red.ofParStar {t u : Term} (h : Star Par t u) : Red t u :=
  Star.flatten Par.toRed h

/-- **Church–Rosser**: β-reduction is confluent. -/
theorem Red.confluent {t u v : Term} (hu : Red t u) (hv : Red t v) :
    ∃ w, Red u w ∧ Red v w := by
  obtain ⟨w, hw1, hw2⟩ := Par.confluent hu.toParStar hv.toParStar
  exact ⟨w, Red.ofParStar hw1, Red.ofParStar hw2⟩

/-! ## Consequences -/

/-- A term is β-normal if it does not reduce. -/
def Normal (t : Term) : Prop := ∀ u, ¬ Step t u

theorem Red.eq_of_normal {t u : Term} (h : Red t u) (ht : Normal t) : u = t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs (ht _)

/-- Normal forms are unique. -/
theorem Red.normal_unique {t u v : Term} (hu : Red t u) (hv : Red t v)
    (nu : Normal u) (nv : Normal v) : u = v := by
  obtain ⟨w, huw, hvw⟩ := Red.confluent hu hv
  rw [← huw.eq_of_normal nu, ← hvw.eq_of_normal nv]

/-- β-conversion: the equivalence relation generated by `Step`. -/
inductive Conv : Term → Term → Prop
  /-- Reflexivity. -/
  | refl (t : Term) : Conv t t
  /-- A forward step. -/
  | fwd {t u v : Term} : Conv t u → Step u v → Conv t v
  /-- A backward step. -/
  | bwd {t u v : Term} : Conv t u → Step v u → Conv t v

/-- Two terms are joinable if they have a common reduct. -/
def Joinable (t u : Term) : Prop := ∃ w, Red t w ∧ Red u w

theorem Joinable.of_conv {t u : Term} (h : Conv t u) : Joinable t u := by
  induction h with
  | refl => exact ⟨_, .refl _, .refl _⟩
  | fwd _ hs ih =>
    obtain ⟨w, htw, huw⟩ := ih
    obtain ⟨x, hwx, hvx⟩ := Red.confluent huw (Star.single hs)
    exact ⟨x, htw.trans hwx, hvx⟩
  | bwd _ hs ih =>
    obtain ⟨w, htw, huw⟩ := ih
    exact ⟨w, htw, Star.head hs huw⟩

/-- Conversion is transitive. -/
theorem Conv.trans {t u v : Term} (h1 : Conv t u) (h2 : Conv u v) : Conv t v := by
  induction h2 with
  | refl => exact h1
  | fwd _ hs ih => exact .fwd ih hs
  | bwd _ hs ih => exact .bwd ih hs

/-- Conversion is symmetric. -/
theorem Conv.symm {t u : Term} (h : Conv t u) : Conv u t := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih => exact Conv.trans (Conv.bwd (.refl _) hs) ih
  | bwd _ hs ih => exact Conv.trans (Conv.fwd (.refl _) hs) ih

theorem Conv.of_red {t u : Term} (h : Red t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .fwd ih hs

/-- **Church–Rosser**, conversion form: β-convertible terms have a common reduct. -/
theorem Conv.joinable {t u : Term} : Conv t u ↔ Joinable t u :=
  ⟨Joinable.of_conv, fun ⟨_, htw, huw⟩ => (Conv.of_red htw).trans (Conv.of_red huw).symm⟩

/-- Distinct normal forms are not β-convertible; in particular, β-conversion is
non-trivial. -/
theorem Conv.normal_eq {t u : Term} (h : Conv t u) (nt : Normal t) (nu : Normal u) : t = u := by
  obtain ⟨w, htw, huw⟩ := Conv.joinable.mp h
  rw [htw.eq_of_normal nt] at huw
  exact huw.eq_of_normal nu

/-! ## Morphisms preserve computation -/

section Translation

variable {σ : Subst} (hσ : σ.Closed) (hl : σ lamN = .const lamN)
include hσ hl

/-- A morphism that fixes `λ` maps reduction steps to reduction steps. (It may create
new redexes, by mapping a constant to a λ-abstraction, but never destroys one.) -/
theorem Step.trans {t u : Term} (h : Step t u) : Step (t.trans σ) (u.trans σ) := by
  induction h with
  | beta A t a =>
    rw [Term.trans_inst hσ]
    have := Step.beta (A.trans σ) (t.trans σ) (a.trans σ)
    simpa [Term.trans, hl] using this
  | appL a _ ih => exact .appL _ ih
  | appR f _ ih => exact .appR _ ih
  | bindB A t _ ih => exact .bindB _ _ ih
  | bindA b t _ ih => exact .bindA _ _ ih
  | bindT b A _ ih => exact .bindT _ _ ih

/-- A morphism that fixes `λ` preserves multi-step reduction. -/
theorem Red.trans {t u : Term} (h : Red t u) : Red (t.trans σ) (u.trans σ) :=
  Star.map (Term.trans σ) (Step.trans hσ hl) h

/-- A morphism that fixes `λ` preserves β-conversion. -/
theorem Conv.trans_mor {t u : Term} (h : Conv t u) : Conv (t.trans σ) (u.trans σ) := by
  induction h with
  | refl => exact .refl _
  | fwd _ hs ih => exact .fwd ih (Step.trans hσ hl hs)
  | bwd _ hs ih => exact .bwd ih (Step.trans hσ hl hs)

end Translation

end MMT.LF
