import MMTFormal.Judgment

/-!
# The MMT module system: theory graphs, flattening, views

This file formalizes the structural level (`api/modules/Theory.scala`,
`api/modules/View.scala`, `api/symbols/Constant.scala`, includes as in
`api/symbols/Structure.scala`):

* a `Theory` has an optional meta-theory and a list of declarations: constants (with
  optional type and definiens), `include`s of other theories, and `structure`s
  (named, renaming imports of another theory with assignments);
* a `Library` (MMT's `Library`/`Controller` state) maps theory names to theories;
* `Visible L T S` holds if the declarations of `S` are visible in `T`
  (reflexive-transitive closure of include and meta-theory edges);
* `homeInfo L H n` is the declaration of the constant `H?n` in its home theory `H`;
  for a copy `H?s/c` induced by a structure it is the translated declaration of `c`;
* `flat L T` is the flattening of `T`, i.e. the signature against which MMT checks;
* a `View` assigns terms to the local constants of its domain.

Results: include/meta-theory edges induce morphisms; views elaborate to substitutions,
and a view is well-typed if its assignments are (`View.isMorphism_of_check`);
structure declarations induce well-typed morphisms (`structMor_isMorphism`);
well-typed views and structures then translate all judgments by `Derivable.trans`.
-/

namespace MMT

/-- Declarations in a theory body. -/
inductive Decl where
  | const  (name : String) (tp df : Option Term)
  | incl   (thy : ThyName)
  /-- `structure name : dom = assign`: imports `dom` with all constants not already
  visible in the host copied under the prefix `name`; `assign` defines copies. -/
  | struct (name : String) (dom : ThyName) (assign : List (GName × Term))
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
    | _ => none

/-- Lookup of a structure declaration within a single theory body. -/
def Theory.structLookup (th : Theory) (s : String) : Option (ThyName × List (GName × Term)) :=
  th.decls.findSome? fun
    | .struct s' S as => if s' = s then some (S, as) else none
    | _ => none

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
/-- The morphism induced by the structure `s` declared in `H`: constants already
visible in `H` (in particular those of the meta-theory) are shared; all others are
mapped to their copies `H?s/c`. -/
noncomputable def structMor (L : Library) (H : ThyName) (s : String) : Subst := fun c =>
  if Visible L H c.thy then .const c else .const ⟨H, .sub s c.thy c.name⟩

open Classical in
/-- The declaration of the constant `H?n` in its home theory `H`. Copies induced by a
structure `s : Sdom` are declared with their original type translated along the
structure, and their definiens given by the assignment or translated. Structural
recursion on the local name. -/
noncomputable def homeInfo (L : Library) : ThyName → LName → Option ConstInfo
  | H, .base n => (L H).bind (·.localLookup n)
  | H, .sub s S0 orig =>
    match (L H).bind (·.structLookup s) with
    | some (Sdom, as) =>
      if Visible L Sdom S0 ∧ ¬ Visible L H S0 then
        (homeInfo L S0 orig).map fun i =>
          ⟨i.tp.map (·.trans (structMor L H s)),
           (as.lookup ⟨S0, orig⟩).or (i.df.map (·.trans (structMor L H s)))⟩
      else none
    | none => none

open Classical in
/-- Flattening: the signature of all constants visible in `T`. Global names are
qualified by their home theory, so a constant `⟨S, n⟩` is in `flat L T` iff `S` is
visible in `T` and declares `n` (possibly as a structure copy). -/
noncomputable def flat (L : Library) (T : ThyName) : Sig := fun c =>
  if Visible L T c.thy then homeInfo L c.thy c.name else none

theorem flat_eq_some {L : Library} {T : ThyName} {c : GName} {i : ConstInfo} :
    flat L T c = some i ↔ Visible L T c.thy ∧ homeInfo L c.thy c.name = some i := by
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
  assign : List (LName × Term)
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

theorem List.lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {n : α} {t : β}
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

/-! ## Structures -/

theorem structMor_shared {L : Library} {H : ThyName} {s : String} {c : GName}
    (h : Visible L H c.thy) : structMor L H s c = .const c := by
  simp [structMor, h]

theorem structMor_copy {L : Library} {H : ThyName} {s : String} {c : GName}
    (h : ¬ Visible L H c.thy) : structMor L H s c = .const ⟨H, .sub s c.thy c.name⟩ := by
  simp [structMor, h]

/-- The copy of a non-shared constant `c` of the domain is declared in the host. -/
theorem homeInfo_copy {L : Library} {H Sdom : ThyName} {s : String}
    {as : List (GName × Term)} (hs : (L H).bind (·.structLookup s) = some (Sdom, as))
    {S0 : ThyName} {n : LName} {i : ConstInfo}
    (hv : Visible L Sdom S0) (hnv : ¬ Visible L H S0) (hi : homeInfo L S0 n = some i) :
    homeInfo L H (.sub s S0 n) =
      some ⟨i.tp.map (·.trans (structMor L H s)),
        (as.lookup ⟨S0, n⟩).or (i.df.map (·.trans (structMor L H s)))⟩ := by
  have hc : (Visible L Sdom S0 ∧ ¬ Visible L H S0) := ⟨hv, hnv⟩
  simp only [homeInfo, hs, hc, hi]
  rfl

/-- **Structures induce morphisms.** If `H` declares `structure s : Sdom = as`, then the
induced map is a well-typed morphism from `Sdom` into `H`, provided
* the meta-symbols of the foundation are visible in `H` (shared meta-theory),
* declarations of shared constants only refer to constants visible in their home
  theory (which holds for well-formed theories), and
* assignments are only made to undefined constants.

This is the module-level counterpart of `Structure.isMorphism` for pushouts. -/
theorem structMor_isMorphism {F : Foundation} {L : Library} {H Sdom : ThyName} {s : String}
    {as : List (GName × Term)} (hs : (L H).bind (·.structLookup s) = some (Sdom, as))
    (hmeta : ∀ c, F.metaSym c → Visible L H c.thy)
    (hscoped : ∀ c i, flat L Sdom c = some i → Visible L H c.thy →
      (∀ A, i.tp = some A → A.UsesOnly (fun d => Visible L c.thy d.thy)) ∧
      (∀ e, i.df = some e → e.UsesOnly (fun d => Visible L c.thy d.thy)))
    (hassign : ∀ c t, as.lookup c = some t → ∀ i, flat L Sdom c = some i → i.df = none) :
    IsMorphism F (flat L Sdom) (flat L H) (structMor L H s) := by
  -- on the declarations of shared constants, the structure acts as the identity
  have hfix : ∀ {c : GName} (x : Term), Visible L H c.thy →
      x.UsesOnly (fun d => Visible L c.thy d.thy) → x.trans (structMor L H s) = x := by
    intro c x hc hx
    rw [Term.trans_congr (τ := Subst.id) hx
      (fun d hd => structMor_shared (hc.trans hd)), Term.trans_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c; unfold structMor; split <;> trivial
  · intro c hc; exact structMor_shared (hmeta c hc)
  · intro c A d hc
    obtain ⟨hv, hh⟩ := flat_eq_some.mp hc
    by_cases hsh : Visible L H c.thy
    · rw [structMor_shared hsh, hfix A hsh ((hscoped c _ hc hsh).1 A rfl)]
      exact .const (flat_eq_some.mpr ⟨hsh, hh⟩)
    · rw [structMor_copy hsh]
      exact .const (d := _) (flat_eq_some.mpr ⟨.refl _, homeInfo_copy hs hv hsh hh⟩)
  · intro c A d hc
    obtain ⟨hv, hh⟩ := flat_eq_some.mp hc
    by_cases hsh : Visible L H c.thy
    · rw [structMor_shared hsh, hfix A hsh ((hscoped c _ hc hsh).1 A rfl),
        hfix d hsh ((hscoped c _ hc hsh).2 d rfl)]
      exact .defn (flat_eq_some.mpr ⟨hsh, hh⟩)
    · rw [structMor_copy hsh]
      have ha : as.lookup ⟨c.thy, c.name⟩ = none := by
        cases h : as.lookup ⟨c.thy, c.name⟩ with
        | none => rfl
        | some t => cases hassign c t h _ hc
      have := homeInfo_copy hs hv hsh hh
      rw [ha] at this
      exact .defn (flat_eq_some.mpr ⟨.refl _, this⟩)

/-- Everything derivable in the domain of a structure holds for the copies in the host. -/
theorem structMor_preserves {F : Foundation} {L : Library} {H Sdom : ThyName} {s : String}
    {as : List (GName × Term)} (hs : (L H).bind (·.structLookup s) = some (Sdom, as))
    (hmeta : ∀ c, F.metaSym c → Visible L H c.thy)
    (hscoped : ∀ c i, flat L Sdom c = some i → Visible L H c.thy →
      (∀ A, i.tp = some A → A.UsesOnly (fun d => Visible L c.thy d.thy)) ∧
      (∀ e, i.df = some e → e.UsesOnly (fun d => Visible L c.thy d.thy)))
    (hassign : ∀ c t, as.lookup c = some t → ∀ i, flat L Sdom c = some i → i.df = none)
    {J : Judgment} (hJ : Derivable F (flat L Sdom) J) :
    Derivable F (flat L H) (J.trans (structMor L H s)) :=
  Derivable.trans (structMor_isMorphism hs hmeta hscoped hassign) hJ

/-- Copies induced by structures are inherited along includes: every theory that sees
the host also sees the copies, and the structure composed with the inclusion is still
a morphism. -/
theorem structMor_isMorphism_incl {F : Foundation} {L : Library} {R H Sdom : ThyName}
    {s : String} {as : List (GName × Term)}
    (hs : (L H).bind (·.structLookup s) = some (Sdom, as)) (hRH : Visible L R H)
    (hmeta : ∀ c, F.metaSym c → Visible L H c.thy)
    (hscoped : ∀ c i, flat L Sdom c = some i → Visible L H c.thy →
      (∀ A, i.tp = some A → A.UsesOnly (fun d => Visible L c.thy d.thy)) ∧
      (∀ e, i.df = some e → e.UsesOnly (fun d => Visible L c.thy d.thy)))
    (hassign : ∀ c t, as.lookup c = some t → ∀ i, flat L Sdom c = some i → i.df = none) :
    IsMorphism F (flat L Sdom) (flat L R) ((structMor L H s).comp Subst.id) :=
  (structMor_isMorphism hs hmeta hscoped hassign).comp (hRH.isMorphism F)

end MMT
