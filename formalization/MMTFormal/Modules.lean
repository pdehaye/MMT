import MMTFormal.Judgment

/-!
# The MMT module system: theory graphs, flattening, views

This file formalizes the structural level (`api/modules/Theory.scala`,
`api/modules/View.scala`, `api/symbols/Constant.scala`, includes as in
`api/symbols/Structure.scala`):

* a `Theory` has an optional meta-theory and a list of declarations, each either a
  constant (with optional type and definiens) or an `include` of another theory;
* a `Library` (MMT's `Library`/`Controller` state) maps theory names to theories;
* `Visible L T S` holds if the declarations of `S` are visible in `T`
  (reflexive-transitive closure of include and meta-theory edges);
* `flat L T` is the flattening of `T`, i.e. the signature against which MMT checks;
* a `View` assigns terms to the local constants of its domain.

Results: include/meta-theory edges induce morphisms; views elaborate to substitutions,
and a view is well-typed if its assignments are (`View.isMorphism_of_check`);
well-typed views then translate all judgments by `Derivable.trans`.
-/

namespace MMT

/-- Declarations in a theory body. -/
inductive Decl where
  | const (name : String) (tp df : Option Term)
  | incl  (thy : ThyName)
deriving DecidableEq, Repr

structure Theory where
  metaThy : Option ThyName
  decls   : List Decl
deriving Repr

/-- The theory graph currently loaded. -/
abbrev Library := ThyName → Option Theory

/-- Lookup of a local constant within a single theory body. -/
def Theory.localLookup (th : Theory) (n : String) : Option ConstInfo :=
  th.decls.findSome? fun
    | .const n' tp df => if n' = n then some ⟨tp, df⟩ else none
    | .incl _ => none

/-- `Visible L T S`: the declarations of `S` are visible in `T`. -/
inductive Visible (L : Library) : ThyName → ThyName → Prop where
  | refl (T) : Visible L T T
  | incl {T S R th} : L T = some th → .incl S ∈ th.decls → Visible L S R → Visible L T R
  | metaThy {T M R th} : L T = some th → th.metaThy = some M → Visible L M R → Visible L T R

theorem Visible.trans {L : Library} {T S R : ThyName}
    (h₁ : Visible L T S) (h₂ : Visible L S R) : Visible L T R := by
  induction h₁ with
  | refl => exact h₂
  | incl hT hS _ ih => exact .incl hT hS (ih h₂)
  | metaThy hT hM _ ih => exact .metaThy hT hM (ih h₂)

open Classical in
/-- Flattening: the signature of all constants visible in `T`. Global names are
qualified by their home theory, so a constant `⟨S, n⟩` is in `flat L T` iff `S` is
visible in `T` and declares `n`. -/
noncomputable def flat (L : Library) (T : ThyName) : Sig := fun c =>
  if Visible L T c.thy then (L c.thy).bind (·.localLookup c.name) else none

theorem flat_eq_some {L : Library} {T : ThyName} {c : GName} {i : ConstInfo} :
    flat L T c = some i ↔ Visible L T c.thy ∧ (L c.thy).bind (·.localLookup c.name) = some i := by
  unfold flat; split <;> simp_all

/-- Visibility induces signature inclusion of the flattenings. -/
theorem flat_sub {L : Library} {T S : ThyName} (h : Visible L T S) : (flat L S).Sub (flat L T) := by
  intro c i hc
  obtain ⟨hv, hl⟩ := flat_eq_some.mp hc
  exact flat_eq_some.mpr ⟨h.trans hv, hl⟩

/-- Every include (and meta-theory) edge, and every path of such edges, is a
well-typed morphism, regardless of foundation. -/
theorem Visible.isMorphism {L : Library} {T S : ThyName} (F : Foundation) (h : Visible L T S) :
    IsMorphism F (flat L S) (flat L T) Subst.id :=
  IsMorphism.incl (flat_sub h)

/-! ## Views -/

/-- A view `dom → cod` with assignments to local constants of `dom`. -/
structure View where
  dom    : ThyName
  cod    : ThyName
  assign : List (String × Term)
deriving Repr

/-- Elaboration of a view to its action on constants. Constants of `dom` with an
assignment are mapped to it; all other constants (meta-theory, includes shared with
the codomain) are mapped to themselves. -/
def View.toSubst (v : View) : Subst := fun c =>
  if c.thy = v.dom then
    match v.assign.lookup c.name with
    | some t => t
    | none   => .const c
  else .const c

/-- A view is well-typed if its elaboration is a morphism between the flattenings. -/
def View.WellTyped (F : Foundation) (L : Library) (v : View) : Prop :=
  IsMorphism F (flat L v.dom) (flat L v.cod) v.toSubst

theorem List.lookup_mem {l : List (String × Term)} {n : String} {t : Term}
    (h : l.lookup n = some t) : (n, t) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨m, s⟩ := p
    by_cases hm : n = m
    · subst hm; simp [List.lookup] at h; subst h; simp
    · have : (n == m) = false := by simpa using hm
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem View.toSubst_closed {v : View} (hcl : ∀ p ∈ v.assign, p.2.ClosedAt 0) :
    v.toSubst.Closed := by
  intro c
  unfold toSubst
  split
  · split
    · rename_i t ht; exact hcl _ (List.lookup_mem ht)
    · trivial
  · trivial

theorem View.toSubst_other {v : View} {c : GName} (h : c.thy ≠ v.dom) :
    v.toSubst c = .const c := by
  simp [toSubst, h]

/-- **View checking.** To show a view well-typed it suffices that
1. all assignments are closed and the meta-theory is not the domain;
2. every local constant of the domain is mapped to a term of the translated type
   (and respects definitions) — this is what MMT's checker verifies per assignment;
3. constants of other theories visible in the domain are also available, unchanged,
   in the codomain, and their types/definitions do not mention the domain's constants
   (e.g. the domain and codomain share a meta-theory such as LF). -/
theorem View.isMorphism_of_check {F : Foundation} {L : Library} {v : View}
    (hcl : ∀ p ∈ v.assign, p.2.ClosedAt 0)
    (hmeta : ∀ c, F.metaSym c → c.thy ≠ v.dom)
    (hloc : ∀ n A d, flat L v.dom ⟨v.dom, n⟩ = some ⟨some A, d⟩ →
      Derivable F (flat L v.cod) (.typing [] (v.toSubst ⟨v.dom, n⟩) (A.trans v.toSubst)) ∧
      ∀ e, d = some e →
        Derivable F (flat L v.cod)
          (.equal [] (v.toSubst ⟨v.dom, n⟩) (e.trans v.toSubst) (A.trans v.toSubst)))
    (hshared : ∀ c i, c.thy ≠ v.dom → flat L v.dom c = some i →
      flat L v.cod c = some i ∧
      (∀ A, i.tp = some A → A.trans v.toSubst = A) ∧
      (∀ e, i.df = some e → e.trans v.toSubst = e)) :
    v.WellTyped F L where
  closed := toSubst_closed hcl
  fixMeta c hc := toSubst_other (hmeta c hc)
  typed {c A d} hc := by
    by_cases h : c.thy = v.dom
    · obtain ⟨t, n⟩ := c
      simp only at h; subst h
      exact (hloc n A d hc).1
    · obtain ⟨hcod, htp, -⟩ := hshared c _ h hc
      rw [toSubst_other h, htp A rfl]
      exact .const hcod
  defn {c A d} hc := by
    by_cases h : c.thy = v.dom
    · obtain ⟨t, n⟩ := c
      simp only at h; subst h
      exact (hloc n A (some d) hc).2 d rfl
    · obtain ⟨hcod, htp, hdf⟩ := hshared c _ h hc
      rw [toSubst_other h, htp A rfl, hdf d rfl]
      exact .defn hcod

/-- A well-typed view translates every judgment of its domain into one of its codomain. -/
theorem View.WellTyped.preserves {F : Foundation} {L : Library} {v : View}
    (hv : v.WellTyped F L) {J : Judgment} (h : Derivable F (flat L v.dom) J) :
    Derivable F (flat L v.cod) (J.trans v.toSubst) :=
  Derivable.trans hv h

end MMT
