import MMTlib.Diagrams.Basic
import MMTlib.Modules.Basic

/-!
# Meta-operators on diagrams

MMT's diagram expressions (`api/modules/diagrams/Diagram.scala`, `MetaOperators.scala`,
`ZippingOperator.scala`) combine diagrams before or after operators are applied. A
diagram there is a list of module names together with an optional *meta-diagram*.

This file formalizes, on such diagrams of names over a `Library`:
* `union` (`UnionDiagramOperator`): distinct union of modules, recursive union of meta-diagrams;
* `difference` (`DifferenceOperator`): remove the modules of another diagram;
* `rebase` (`RebaseOperator`): replace the meta-diagram;
* `subsumes` (`Diagram.subsumes`): every module of the other diagram includes one of ours;
* `closure` (`ClosureDiagramOperator`): all theories reachable by includes and structures
  that are not already part of the meta-diagram.

On the typed diagrams of `Diagrams.lean`:
* `Diagram.sequenced` (`SequencedDiagramOperators`): apply several functors to the *same*
  diagram and take the union of the results;
* `Diagram.zipped` (`ZippingOperator`): apply several functors in parallel, optionally
  keeping only the result of one of them (the *focus*).

Main results: membership characterizations for union, difference and rebase; union
subsumes both arguments; `closure_complete` and `InClosure.closed`: the closure together
with the meta-diagram is closed under dependencies; `closure_iff`: the iterative
computation (`closureN`) computes exactly the relational closure; preservation of
well-formedness by sequencing and zipping.
-/

namespace MMT

/-- A diagram of module names with an optional meta-diagram. -/
inductive NDiagram where
  /-- A list of module names with an optional meta-diagram. -/
  | mk (modules : List ThyName) (mt : Option NDiagram)

namespace NDiagram

/-- The modules of a diagram. -/
def modules : NDiagram → List ThyName
  | mk ms _ => ms

/-- The meta-diagram of a diagram, if any. -/
def metaD : NDiagram → Option NDiagram
  | mk _ m => m

/-- All modules, including those of the meta-diagram (recursively). -/
def allModules : NDiagram → List ThyName
  | mk ms none => ms
  | mk ms (some m) => ms ++ allModules m

/-- Distinct union of name lists. -/
def unionList (a b : List ThyName) : List ThyName := a ++ b.filter (fun x => !(a.contains x))

theorem mem_unionList {a b : List ThyName} {x : ThyName} :
    x ∈ unionList a b ↔ x ∈ a ∨ x ∈ b := by
  unfold unionList
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact .inl h
    · exact .inr (List.mem_filter.mp h).1
  · rintro (h | h)
    · exact List.mem_append_left _ h
    · by_cases ha : x ∈ a
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h, by simpa using ha⟩)

theorem nodup_unionList {a b : List ThyName} (ha : a.Nodup) (hb : b.Nodup) :
    (unionList a b).Nodup := by
  unfold unionList
  rw [List.nodup_append]
  refine ⟨ha, hb.filter _, ?_⟩
  intro x hx y hy hxy
  subst hxy
  have := (List.mem_filter.mp hy).2
  simp [hx] at this

/-- `UnionDiagramOperator`. -/
def union : NDiagram → NDiagram → NDiagram
  | mk a none, mk b mb => mk (unionList a b) mb
  | mk a (some ma), mk b none => mk (unionList a b) (some ma)
  | mk a (some ma), mk b (some mb) => mk (unionList a b) (some (union ma mb))

theorem modules_union (D E : NDiagram) :
    (D.union E).modules = unionList D.modules E.modules := by
  obtain ⟨a, ma⟩ := D; obtain ⟨b, mb⟩ := E
  cases ma <;> cases mb <;> rfl

theorem mem_union_modules {D E : NDiagram} {x : ThyName} :
    x ∈ (D.union E).modules ↔ x ∈ D.modules ∨ x ∈ E.modules := by
  rw [modules_union, mem_unionList]

theorem mem_allModules_union : ∀ {D E : NDiagram} {x : ThyName},
    x ∈ (D.union E).allModules ↔ x ∈ D.allModules ∨ x ∈ E.allModules
  | mk a none, mk b none, x => by simp [union, allModules, mem_unionList]
  | mk a none, mk b (some mb), x => by
    simp [union, allModules, mem_unionList, or_assoc]
  | mk a (some ma), mk b none, x => by
    simp [union, allModules, mem_unionList, or_assoc, or_comm, or_left_comm]
  | mk a (some ma), mk b (some mb), x => by
    simp only [union, allModules, List.mem_append, mem_unionList]
    rw [mem_allModules_union (D := ma) (E := mb)]
    simp [or_assoc, or_left_comm]

/-- `DifferenceOperator`: keep the modules not in the other diagram, and the meta-diagram. -/
def difference (D E : NDiagram) : NDiagram :=
  mk (D.modules.filter (fun x => !(E.modules.contains x))) D.metaD

theorem mem_difference {D E : NDiagram} {x : ThyName} :
    x ∈ (D.difference E).modules ↔ x ∈ D.modules ∧ x ∉ E.modules := by
  simp [difference, modules, List.mem_filter]

theorem metaD_difference (D E : NDiagram) : (D.difference E).metaD = D.metaD := by
  obtain ⟨a, ma⟩ := D; rfl

/-- `RebaseOperator`: replace the meta-diagram. -/
def rebase (D M : NDiagram) : NDiagram := mk D.modules (some M)

theorem allModules_rebase (D M : NDiagram) :
    (D.rebase M).allModules = D.modules ++ M.allModules := rfl

/-! ## Subsumption -/

/-- `hasImplicitTo`: some module of `D` (or its meta-diagram) is included in `T`. -/
def HasImplicitTo (L : Library) (D : NDiagram) (T : ThyName) : Prop :=
  ∃ m ∈ D.allModules, Visible L T m

/-- `subsumes`: the meta-diagram of `E` is subsumed, and every module of `E` includes a
module of `D`. -/
def Subsumes (L : Library) : NDiagram → NDiagram → Prop
  | D, mk ms none => ∀ T ∈ ms, HasImplicitTo L D T
  | D, mk ms (some m) => Subsumes L D m ∧ ∀ T ∈ ms, HasImplicitTo L D T

theorem modules_sub_allModules (D : NDiagram) : ∀ x ∈ D.modules, x ∈ D.allModules := by
  intro x hx; obtain ⟨a, ma⟩ := D; cases ma <;> simp_all [modules, allModules]

theorem hasImplicitTo_mono {L : Library} {D D' : NDiagram}
    (h : ∀ x ∈ D.allModules, x ∈ D'.allModules) {T : ThyName} (hT : HasImplicitTo L D T) :
    HasImplicitTo L D' T := by
  obtain ⟨m, hm, hv⟩ := hT; exact ⟨m, h m hm, hv⟩

theorem subsumes_mono {L : Library} {D D' : NDiagram}
    (h : ∀ x ∈ D.allModules, x ∈ D'.allModules) : ∀ E, Subsumes L D E → Subsumes L D' E
  | mk _ none, hE => fun T hT => hasImplicitTo_mono h (hE T hT)
  | mk _ (some m), hE => ⟨subsumes_mono h m hE.1, fun T hT => hasImplicitTo_mono h (hE.2 T hT)⟩

/-- A diagram subsumes every diagram whose modules it contains. -/
theorem subsumes_of_sub (L : Library) : ∀ (E D : NDiagram),
    (∀ x ∈ E.allModules, x ∈ D.allModules) → Subsumes L D E
  | mk ms none, D, h => fun T hT => ⟨T, h T (by simpa [allModules] using hT), .refl _⟩
  | mk ms (some m), D, h =>
    ⟨subsumes_of_sub L m D (fun x hx => h x (by simp [allModules, hx])),
     fun T hT => ⟨T, h T (by simp [allModules, hT]), .refl _⟩⟩

/-- Every diagram subsumes itself. -/
theorem subsumes_refl (L : Library) (D : NDiagram) : Subsumes L D D :=
  subsumes_of_sub L D D (fun _ h => h)

/-- The union subsumes both arguments. -/
theorem union_subsumes_left (L : Library) (D E : NDiagram) : Subsumes L (D.union E) D :=
  subsumes_of_sub L D _ (fun _ hx => mem_allModules_union.mpr (.inl hx))

theorem union_subsumes_right (L : Library) (D E : NDiagram) : Subsumes L (D.union E) E :=
  subsumes_of_sub L E _ (fun _ hx => mem_allModules_union.mpr (.inr hx))

/-! ## Closure -/

/-- The modules a theory refers to: its includes and the domains of its structures. -/
def refs (L : Library) (T : ThyName) : List ThyName :=
  match L T with
  | some th => th.decls.filterMap fun
      | .incl S => some S
      | .struct _ S _ => some S
      | _ => none
  | none => []

/-- `T` belongs to the meta-diagram `M`: some module of `M` includes it. -/
def MetaSub (L : Library) (M : NDiagram) (T : ThyName) : Prop :=
  ∃ m ∈ M.allModules, Visible L m T

/-- The closure of a list of modules with respect to a meta-diagram: everything reachable
by includes and structures, stopping at modules of the meta-diagram. -/
inductive InClosure (L : Library) (D : List ThyName) (M : NDiagram) : ThyName → Prop where
  /-- A starting module outside the meta-diagram. -/
  | base {T} : T ∈ D → ¬ MetaSub L M T → InClosure L D M T
  /-- A dependency of a module in the closure, outside the meta-diagram. -/
  | step {S R} : InClosure L D M S → R ∈ refs L S → ¬ MetaSub L M R → InClosure L D M R

/-- **Dependency closure**: every dependency of a module in the closure is in the closure
or belongs to the meta-diagram. -/
theorem InClosure.closed {L : Library} {D : List ThyName} {M : NDiagram} {S R : ThyName}
    (hS : InClosure L D M S) (hR : R ∈ refs L S) : InClosure L D M R ∨ MetaSub L M R := by
  by_cases h : MetaSub L M R
  · exact .inr h
  · exact .inl (.step hS hR h)

/-- The closure contains no module of the meta-diagram. -/
theorem InClosure.not_meta {L : Library} {D : List ThyName} {M : NDiagram} {T : ThyName}
    (h : InClosure L D M T) : ¬ MetaSub L M T := by
  cases h with
  | base _ h => exact h
  | step _ _ h => exact h

/-- The closure is the least set containing the starting modules and closed under
non-meta dependencies. -/
theorem InClosure.least {L : Library} {D : List ThyName} {M : NDiagram} (P : ThyName → Prop)
    (hbase : ∀ T ∈ D, ¬ MetaSub L M T → P T)
    (hstep : ∀ S R, P S → R ∈ refs L S → ¬ MetaSub L M R → P R) {T : ThyName}
    (h : InClosure L D M T) : P T := by
  induction h with
  | base hT hm => exact hbase _ hT hm
  | step _ hR hm ih => exact hstep _ _ ih hR hm

open Classical in
/-- The iterative computation of the closure (as MMT's breadth-first search does). -/
noncomputable def closureN (L : Library) (D : List ThyName) (M : NDiagram) : Nat → List ThyName
  | 0 => D.filter fun T => decide (¬ MetaSub L M T)
  | n + 1 =>
    let cur := closureN L D M n
    cur ++ (cur.flatMap (refs L)).filter fun T => decide (¬ MetaSub L M T)

theorem closureN_mono {L : Library} {D : List ThyName} {M : NDiagram} {n : Nat} {T : ThyName}
    (h : T ∈ closureN L D M n) : T ∈ closureN L D M (n + 1) := by
  simp only [closureN]; exact List.mem_append_left _ h

/-- **The iteration computes the closure**: a module is in the closure iff it is reached
after finitely many rounds. -/
theorem closure_iff {L : Library} {D : List ThyName} {M : NDiagram} {T : ThyName} :
    InClosure L D M T ↔ ∃ n, T ∈ closureN L D M n := by
  constructor
  · intro h
    induction h with
    | base hT hm => exact ⟨0, by simp [closureN, hT, hm]⟩
    | @step S R _ hR hm ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      simp only [closureN]
      exact List.mem_append_right _
        (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨S, hn, hR⟩, by simpa using hm⟩)
  · rintro ⟨n, hn⟩
    induction n generalizing T with
    | zero =>
      simp only [closureN, List.mem_filter, decide_eq_true_eq] at hn
      exact .base hn.1 hn.2
    | succ n ih =>
      simp only [closureN] at hn
      rcases List.mem_append.mp hn with h | h
      · exact ih h
      · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
        obtain ⟨S, hS, hR⟩ := List.mem_flatMap.mp h1
        exact .step (ih hS) hR (by simpa using h2)

/-- `ClosureDiagramOperator`: close the modules of `D` with respect to `M`, which becomes
the meta-diagram of the result. -/
noncomputable def closure (L : Library) (D M : NDiagram) (n : Nat) : NDiagram :=
  mk (closureN L D.modules M n) (some M)

/-- **Completeness of the closure**: with enough rounds, every dependency of a module in
the closure is in the closure or in its meta-diagram. -/
theorem closure_complete {L : Library} {D M : NDiagram} {n : Nat} {S R : ThyName}
    (hS : S ∈ (closure L D M n).modules) (hR : R ∈ refs L S) :
    R ∈ (closure L D M (n + 1)).modules ∨ MetaSub L M R := by
  have hS' : InClosure L D.modules M S := closure_iff.mpr ⟨n, hS⟩
  rcases hS'.closed hR with h | h
  · by_cases hm : MetaSub L M R
    · exact .inr hm
    · left
      simp only [closure, modules, closureN]
      exact List.mem_append_right _
        (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨S, hS, hR⟩, by simpa using hm⟩)
  · exact .inr h

/-- The closure only contains genuine dependencies of the starting modules. -/
theorem closure_sound {L : Library} {D M : NDiagram} {n : Nat} {T : ThyName}
    (h : T ∈ (closure L D M n).modules) : InClosure L D.modules M T :=
  closure_iff.mpr ⟨n, h⟩

end NDiagram

/-! ## Sequencing and zipping on typed diagrams -/

namespace Diagram

variable {F : Foundation}

/-- The union of a list of diagrams. -/
def unionAll : List Diagram → Diagram
  | [] => ⟨[], []⟩
  | D :: Ds => D.union (unionAll Ds)

theorem unionAll_wf : ∀ {Ds : List Diagram}, (∀ D ∈ Ds, D.WF F) → (unionAll Ds).WF F
  | [], _ => by intro e he; simp [unionAll] at he
  | D :: Ds, h => union_wf (h D (by simp)) (unionAll_wf (fun D' hD' => h D' (by simp [hD'])))

/-- `SequencedDiagramOperators`: apply each functor to the same diagram and take the union
of the results. -/
def sequenced (Gs : List (LinFunctor F)) (D : Diagram) : Diagram :=
  unionAll (Gs.map fun G => D.map G)

theorem sequenced_wf (Gs : List (LinFunctor F)) {D : Diagram} (h : D.WF F) :
    (sequenced Gs D).WF F :=
  unionAll_wf (fun D' hD' => by
    obtain ⟨G, -, rfl⟩ := List.mem_map.mp hD'
    exact map_wf G h)

/-- `ZippingOperator`: apply functors in parallel, each producing its image of `D` and the
connectors from `D`; with a focus, only the focused functor's result is kept. -/
def zipped (Gs : List (LinFunctor F)) (focus : Option Nat) (D : Diagram) : Diagram :=
  match focus.bind (Gs[·]?) with
  | some G => D.connect G
  | none => unionAll (Gs.map fun G => D.connect G)

theorem zipped_wf (Gs : List (LinFunctor F)) (focus : Option Nat) {D : Diagram}
    (h : D.WF F) : (zipped Gs focus D).WF F := by
  unfold zipped
  split
  · exact connect_wf _ h
  · exact unionAll_wf (fun D' hD' => by
      obtain ⟨G, -, rfl⟩ := List.mem_map.mp hD'
      exact connect_wf G h)

end Diagram

end MMT
