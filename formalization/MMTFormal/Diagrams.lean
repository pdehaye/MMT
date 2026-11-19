import MMTFormal.Pushout

/-!
# Diagrams and diagram operators

MMT's diagram operators (`api/modules/diagrams`) map whole diagrams of theories and
morphisms to new diagrams, declaration by declaration.

* A `Diagram` is a list of theories (flat signatures) and a list of edges, each a
  morphism between two of them (`Diagram.scala`). It is well-formed if every edge is
  a well-typed morphism.
* A **linear functor** (`LinearFunctor.scala`) maps every theory and every morphism
  declaration-wise. Here we cover systematic renaming (`SystematicRenamer`): every
  constant `c` becomes `ren c`, its type and definition are translated accordingly,
  and the meta-theory is kept.
* A **linear connector** (`LinearConnector.scala`) connects each theory to its image
  by a morphism, natural in the theory.
* Composition of functors and union of diagrams (the other meta-operators are in `DiagramOps.lean`).

Main results:
* `LinFunctor.mor_isMorphism`: functors map well-typed morphisms to well-typed
  morphisms.
* `LinFunctor.mor_id`, `LinFunctor.mor_comp`: the functor laws hold as equations of
  substitutions.
* `LinFunctor.unit_isMorphism`, `LinFunctor.naturality`: the connector `S → F(S)` is
  a natural family of well-typed morphisms.
* `LinFunctor.comp_obj`, `LinFunctor.comp_mor`: composing two functors gives again a
  linear functor.
* `Diagram.map_wf`, `Diagram.connect_wf`, `Diagram.union_wf`: the diagram operators
  preserve well-formedness. `Diagram.map_commutes`: they preserve commuting squares.
-/

namespace MMT

/-! ## Linear functors -/

/-- A linear functor given by a systematic renaming that fixes the foundation's
meta-symbols. -/
structure LinFunctor (F : Foundation) where
  ren : Renaming
  fixMeta : ∀ c, F.metaSym c → ren.fwd c = c

namespace LinFunctor

variable {F : Foundation} (G : LinFunctor F)

/-- The renaming as a substitution: the action of the connector `S → G(S)`. -/
def unit : Subst := fun c => .const (G.ren.fwd c)

/-- Action on declarations. -/
def info (i : ConstInfo) : ConstInfo :=
  ⟨i.tp.map (·.trans G.unit), i.df.map (·.trans G.unit)⟩

/-- Action on theories. -/
def obj (S : Sig) : Sig := fun d => (G.ren.bwd d).bind fun c => (S c).map G.info

/-- Action on morphisms: `G(σ)(ren c) = ren(σ c)`. -/
def mor (σ : Subst) : Subst := fun d =>
  match G.ren.bwd d with
  | some c => (σ c).trans G.unit
  | none => .const d

variable {G}

theorem unit_closed : G.unit.Closed := fun _ => trivial

theorem obj_fwd (S : Sig) (c : GName) : G.obj S (G.ren.fwd c) = (S c).map G.info := by
  simp [obj, G.ren.bwd_fwd]

theorem mor_fwd (σ : Subst) (c : GName) : G.mor σ (G.ren.fwd c) = (σ c).trans G.unit := by
  simp [mor, G.ren.bwd_fwd]

/-- **Naturality** of the connector: `σ ; unit = unit ; G(σ)`. -/
theorem naturality (σ : Subst) : σ.comp G.unit = G.unit.comp (G.mor σ) := by
  funext c; simp [Subst.comp, unit, Term.trans, mor_fwd]

theorem unit_mor (σ : Subst) (x : Term) :
    (x.trans G.unit).trans (G.mor σ) = (x.trans σ).trans G.unit := by
  rw [← Term.trans_comp, ← naturality, Term.trans_comp]

/-- The connector `S → G(S)` is a well-typed morphism. -/
theorem unit_isMorphism (S : Sig) : IsMorphism F S (G.obj S) G.unit where
  closed := unit_closed
  fixMeta c hc := by simp [unit, G.fixMeta c hc]
  typed {c A d} hc := .const (d := d.map (·.trans G.unit)) (by simp [obj_fwd, hc, info])
  defn {c A d} hc := .defn (by simp [obj_fwd, hc, info])

/-- Functors map well-typed morphisms to well-typed morphisms. -/
theorem mor_isMorphism {S T : Sig} {σ : Subst} (hσ : IsMorphism F S T σ) :
    IsMorphism F (G.obj S) (G.obj T) (G.mor σ) where
  closed d := by
    unfold mor; split
    · exact (hσ.closed _).trans unit_closed
    · trivial
  fixMeta d hd := by
    have : d = G.ren.fwd d := (G.fixMeta d hd).symm
    rw [this, mor_fwd, hσ.fixMeta d hd]
    simp [Term.trans, unit, G.fixMeta d hd]
  typed {d A e} hd := by
    obtain ⟨c, hb, hc⟩ := Option.bind_eq_some_iff.mp hd
    obtain rfl := G.ren.fwd_bwd c d hb
    obtain ⟨⟨tp, df⟩, hi, hinfo⟩ := Option.map_eq_some_iff.mp hc
    simp only [info, ConstInfo.mk.injEq] at hinfo
    obtain ⟨A₀, rfl, rfl⟩ := Option.map_eq_some_iff.mp hinfo.1
    rw [mor_fwd, unit_mor]
    simpa [Judgment.trans] using Derivable.trans (unit_isMorphism T) (hσ.typed hi)
  defn {d A e} hd := by
    obtain ⟨c, hb, hc⟩ := Option.bind_eq_some_iff.mp hd
    obtain rfl := G.ren.fwd_bwd c d hb
    obtain ⟨⟨tp, df⟩, hi, hinfo⟩ := Option.map_eq_some_iff.mp hc
    simp only [info, ConstInfo.mk.injEq] at hinfo
    obtain ⟨A₀, rfl, rfl⟩ := Option.map_eq_some_iff.mp hinfo.1
    obtain ⟨e₀, rfl, rfl⟩ := Option.map_eq_some_iff.mp hinfo.2
    rw [mor_fwd, unit_mor, unit_mor]
    simpa [Judgment.trans] using Derivable.trans (unit_isMorphism T) (hσ.defn hi)

/-- Functor law: identities. -/
theorem mor_id : G.mor Subst.id = Subst.id := by
  funext d
  unfold mor
  split
  · rename_i c hb; obtain rfl := G.ren.fwd_bwd c d hb; rfl
  · rfl

/-- Functor law: composition. -/
theorem mor_comp (σ τ : Subst) : G.mor (σ.comp τ) = (G.mor σ).comp (G.mor τ) := by
  funext d
  cases hb : G.ren.bwd d with
  | none => simp [mor, hb, Subst.comp, Term.trans]
  | some c =>
    obtain rfl := G.ren.fwd_bwd c d hb
    simp only [Subst.comp, mor_fwd]
    rw [unit_mor]

/-! ## Composing functors -/

/-- Sequential composition of renamings. -/
def _root_.MMT.Renaming.comp (ρ₁ ρ₂ : Renaming) : Renaming where
  fwd c := ρ₂.fwd (ρ₁.fwd c)
  bwd d := (ρ₂.bwd d).bind ρ₁.bwd
  bwd_fwd c := by simp [ρ₁.bwd_fwd, ρ₂.bwd_fwd]
  fwd_bwd c d h := by
    obtain ⟨e, he, hc⟩ := Option.bind_eq_some_iff.mp h
    rw [ρ₁.fwd_bwd c e hc, ρ₂.fwd_bwd e d he]

/-- Composition of linear functors: applying `G₂` to the output of `G₁`. (MMT expresses this by nesting operator applications; `SequencedDiagramOperators` is the union of results, see `DiagramOps.lean`.) -/
def comp (G₁ G₂ : LinFunctor F) : LinFunctor F where
  ren := G₁.ren.comp G₂.ren
  fixMeta c hc := by simp [Renaming.comp, G₁.fixMeta c hc, G₂.fixMeta c hc]

theorem comp_unit (G₁ G₂ : LinFunctor F) : (G₁.comp G₂).unit = G₁.unit.comp G₂.unit := by
  funext c; rfl

theorem comp_info (G₁ G₂ : LinFunctor F) (i : ConstInfo) :
    (G₁.comp G₂).info i = G₂.info (G₁.info i) := by
  obtain ⟨tp, df⟩ := i
  cases tp <;> cases df <;> simp [info, comp_unit, Term.trans_comp]

theorem comp_obj (G₁ G₂ : LinFunctor F) (S : Sig) :
    (G₁.comp G₂).obj S = G₂.obj (G₁.obj S) := by
  funext d
  change ((G₂.ren.bwd d).bind G₁.ren.bwd).bind (fun c => (S c).map (G₁.comp G₂).info) =
    (G₂.ren.bwd d).bind fun e => ((G₁.ren.bwd e).bind fun c => (S c).map G₁.info).map G₂.info
  cases G₂.ren.bwd d with
  | none => rfl
  | some e =>
    cases hc : G₁.ren.bwd e with
    | none => simp [hc]
    | some c => cases hS : S c <;> simp [hc, hS, comp_info]

theorem comp_mor (G₁ G₂ : LinFunctor F) (σ : Subst) :
    (G₁.comp G₂).mor σ = G₂.mor (G₁.mor σ) := by
  funext d
  cases hb : G₂.ren.bwd d with
  | none => simp [mor, comp, Renaming.comp, hb]
  | some e =>
    obtain rfl := G₂.ren.fwd_bwd e d hb
    cases hc : G₁.ren.bwd e with
    | none =>
      simp [mor, comp, Renaming.comp, G₂.ren.bwd_fwd, hc, Term.trans, unit]
    | some c =>
      obtain rfl := G₁.ren.fwd_bwd c e hc
      rw [mor_fwd, mor_fwd]
      exact (mor_fwd (G := G₁.comp G₂) σ c).trans (by rw [comp_unit, Term.trans_comp])

end LinFunctor

/-! ## Diagrams -/

/-- A diagram: theories and morphisms between them (edges `(source, target, σ)`). -/
structure Diagram where
  nodes : List Sig
  edges : List (Nat × Nat × Subst)

namespace Diagram

variable {F : Foundation}

/-- All edges are well-typed morphisms between existing nodes. -/
def WF (F : Foundation) (D : Diagram) : Prop :=
  ∀ e ∈ D.edges, ∃ S T, D.nodes[e.1]? = some S ∧ D.nodes[e.2.1]? = some T ∧
    IsMorphism F S T e.2.2

/-- Applying a linear functor to a diagram. -/
def map (G : LinFunctor F) (D : Diagram) : Diagram :=
  ⟨D.nodes.map G.obj, D.edges.map fun e => (e.1, e.2.1, G.mor e.2.2)⟩

theorem map_wf (G : LinFunctor F) {D : Diagram} (h : D.WF F) : (D.map G).WF F := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
  obtain ⟨S, T, hS, hT, hσ⟩ := h e₀ he₀
  exact ⟨G.obj S, G.obj T, by simp [map, hS], by simp [map, hT], G.mor_isMorphism hσ⟩

/-- Union of diagrams (`UnionDiagramOperator`): the nodes of the second diagram are
appended and its edges re-indexed. -/
def union (D₁ D₂ : Diagram) : Diagram :=
  ⟨D₁.nodes ++ D₂.nodes,
   D₁.edges ++ D₂.edges.map fun e => (e.1 + D₁.nodes.length, e.2.1 + D₁.nodes.length, e.2.2)⟩

theorem union_wf {D₁ D₂ : Diagram} (h₁ : D₁.WF F) (h₂ : D₂.WF F) : (D₁.union D₂).WF F := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨S, T, hS, hT, hσ⟩ := h₁ e he
    have l₁ : e.1 < D₁.nodes.length := by
      rcases Nat.lt_or_ge e.1 D₁.nodes.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hS
    have l₂ : e.2.1 < D₁.nodes.length := by
      rcases Nat.lt_or_ge e.2.1 D₁.nodes.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hT
    exact ⟨S, T, by simp [union, List.getElem?_append_left l₁, hS],
      by simp [union, List.getElem?_append_left l₂, hT], hσ⟩
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨S, T, hS, hT, hσ⟩ := h₂ e₀ he₀
    refine ⟨S, T, ?_, ?_, hσ⟩
    · simp only [union]
      rw [List.getElem?_append_right (by omega)]; simpa using hS
    · simp only [union]
      rw [List.getElem?_append_right (by omega)]; simpa using hT

/-- The diagram connected to its image under a linear functor (what a functor plus
its connector produce in MMT): `D ∪ G(D)` with the connector edges `i → n + i`. -/
def connect (G : LinFunctor F) (D : Diagram) : Diagram :=
  let U := D.union (D.map G)
  ⟨U.nodes, U.edges ++ (List.range D.nodes.length).map fun i =>
    (i, i + D.nodes.length, G.unit)⟩

theorem connect_wf (G : LinFunctor F) {D : Diagram} (h : D.WF F) : (D.connect G).WF F := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact union_wf h (map_wf G h) e he
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hi : i < D.nodes.length := List.mem_range.mp hi
    refine ⟨D.nodes[i], G.obj D.nodes[i], ?_, ?_, G.unit_isMorphism _⟩
    · simp [connect, union, List.getElem?_append_left hi]
    · simp only [connect, union, map]
      rw [List.getElem?_append_right (by omega)]
      simp [hi]

/-- Diagram operators preserve commutativity: if `σ ; τ = ρ` then
`G(σ) ; G(τ) = G(ρ)`. -/
theorem map_commutes (G : LinFunctor F) {σ τ ρ : Subst} (h : σ.comp τ = ρ) :
    (G.mor σ).comp (G.mor τ) = G.mor ρ := by
  rw [← h, LinFunctor.mor_comp]

end Diagram

end MMT
