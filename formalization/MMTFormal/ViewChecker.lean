import MMTFormal.Unknowns
import MMTFormal.Modules
import MMTFormal.LFMeta

/-!
# A verified view checker

MMT checks a view `v : dom → cod` assignment by assignment (`MMTStructureChecker`): every
constant of the domain must be mapped to a term of the translated type in the codomain.
This file gives an executable version of that check over a `Library`, built from the
sound LF checker, and proves it sound: if it accepts, the view is a well-typed morphism
(`checkView_sound`).

Ingredients:
* `visibleB`: visibility by bounded search, sound w.r.t. `Visible`;
* `flatB`: computable flattening, sound w.r.t. `flat` (it covers constants with base
  names, i.e. not structure copies);
* `reach`: the theories visible from the domain, by bounded search, together with a
  decidable certificate that the list is complete (it is closed under include and
  meta-theory edges).

The checker handles domains whose visible theories declare no structures; it rejects
other views (soundly).
-/

namespace MMT

/-! ## Computable visibility -/

/-- The theories directly visible from `T`: its includes and its meta-theory. -/
def edges (L : Library) (T : ThyName) : List ThyName :=
  match L T with
  | some th => (th.decls.filterMap fun | .incl S => some S | _ => none) ++ th.metaThy.toList
  | none => []

theorem edges_visible {L : Library} {T S : ThyName} (h : S ∈ edges L T) : Visible L T S := by
  unfold edges at h
  split at h
  · rename_i th hth
    rcases List.mem_append.mp h with h | h
    · obtain ⟨d, hd, hds⟩ := List.mem_filterMap.mp h
      cases d with
      | incl S' => cases hds; exact .incl hth hd (.refl _)
      | const => cases hds
      | struct => cases hds
    · cases hm : th.metaThy with
      | none => rw [hm] at h; cases h
      | some M => rw [hm] at h; simp at h; subst h; exact .metaThy hth hm (.refl _)
  · cases h

/-- Visibility by bounded search. -/
def visibleB (L : Library) : Nat → ThyName → ThyName → Bool
  | 0, T, S => T == S
  | n + 1, T, S => T == S || (edges L T).any fun R => visibleB L n R S

theorem visibleB_sound {L : Library} : ∀ {n : Nat} {T S : ThyName},
    visibleB L n T S = true → Visible L T S
  | 0, T, S, h => by simp [visibleB] at h; subst h; exact .refl _
  | n + 1, T, S, h => by
    simp only [visibleB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨R, hR, hv⟩
    · exact .refl _
    · exact (edges_visible hR).trans (visibleB_sound hv)

/-- The theories reached from `T` within `n` rounds. -/
def reach (L : Library) : Nat → ThyName → List ThyName
  | 0, T => [T]
  | n + 1, T => T :: (edges L T).flatMap (reach L n)

theorem self_mem_reach (L : Library) (n : Nat) (T : ThyName) : T ∈ reach L n T := by
  cases n <;> simp [reach]

/-- A list closed under edges contains everything visible from its members. -/
theorem visible_mem_of_closed {L : Library} {Ls : List ThyName}
    (hcl : ∀ R ∈ Ls, ∀ S ∈ edges L R, S ∈ Ls) {T S : ThyName} (hT : T ∈ Ls)
    (h : Visible L T S) : S ∈ Ls := by
  induction h with
  | refl => exact hT
  | incl hth hS _ ih =>
    refine ih (hcl _ hT _ ?_)
    unfold edges; rw [hth]
    exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨_, hS, rfl⟩)
  | metaThy hth hM _ ih =>
    refine ih (hcl _ hT _ ?_)
    simp [edges, hth, hM]

/-- Decidable check that a list is closed under edges. -/
def closedUnderEdges (L : Library) (Ls : List ThyName) : Bool :=
  Ls.all fun R => (edges L R).all fun S => Ls.contains S

theorem closedUnderEdges_sound {L : Library} {Ls : List ThyName}
    (h : closedUnderEdges L Ls = true) : ∀ R ∈ Ls, ∀ S ∈ edges L R, S ∈ Ls := by
  intro R hR S hS
  simp only [closedUnderEdges, List.all_eq_true, List.contains_iff_mem] at h
  exact h R hR S hS

/-- Everything reached is visible. -/
theorem reach_sound {L : Library} : ∀ {n : Nat} {T S : ThyName}, S ∈ reach L n T → Visible L T S
  | 0, T, S, h => by simp [reach] at h; subst h; exact .refl _
  | n + 1, T, S, h => by
    simp only [reach, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨R, hR, hS⟩
    · exact .refl _
    · exact (edges_visible hR).trans (reach_sound hS)

/-- Decidable visibility: `S` was reached from `T`. -/
def visDec (L : Library) (k : Nat) (T S : ThyName) : Bool := (reach L k T).contains S

theorem visDec_sound {L : Library} {k : Nat} {T S : ThyName} (h : visDec L k T S = true) :
    Visible L T S := reach_sound (by simpa [visDec] using h)

/-- With a completeness certificate for `T`, `visDec` decides visibility from `T`. -/
theorem visDec_iff {L : Library} {k : Nat} {T S : ThyName}
    (hc : closedUnderEdges L (reach L k T) = true) : visDec L k T S = true ↔ Visible L T S :=
  ⟨visDec_sound, fun h => by
    simpa [visDec] using visible_mem_of_closed (closedUnderEdges_sound hc) (self_mem_reach L k T) h⟩

/-! ## Computable flattening -/

/-- The structure morphism, with decidable visibility. -/
def structMorB (L : Library) (k : Nat) (H : ThyName) (s : String) : Subst := fun c =>
  if visDec L k H c.thy then .const c else .const ⟨H, .sub s c.thy c.name⟩

theorem structMorB_eq {L : Library} {k : Nat} {H : ThyName} {s : String}
    (hc : closedUnderEdges L (reach L k H) = true) : structMorB L k H s = structMor L H s := by
  funext c
  unfold structMorB structMor
  by_cases h : Visible L H c.thy
  · simp [h, (visDec_iff hc).mpr h]
  · have : visDec L k H c.thy = false := by
      cases e : visDec L k H c.thy
      · rfl
      · exact absurd ((visDec_iff hc).mp e) h
    simp [h, this]

/-- `homeInfo` with decidable visibility. Copies are only produced when the host has a
completeness certificate, so that non-visibility can be decided. -/
def homeInfoB (L : Library) (k : Nat) : ThyName → LName → Option ConstInfo
  | H, .base n => (L H).bind (·.localLookup n)
  | H, .sub s S0 orig =>
    if closedUnderEdges L (reach L k H) then
      match (L H).bind (·.structLookup s) with
      | some (Sdom, as) =>
        if visDec L k Sdom S0 && !visDec L k H S0 then
          (homeInfoB L k S0 orig).map fun i =>
            ⟨i.tp.map (·.trans (structMorB L k H s)),
             (as.lookup ⟨S0, orig⟩).or (i.df.map (·.trans (structMorB L k H s)))⟩
        else none
      | none => none
    else none

theorem homeInfoB_sound {L : Library} {k : Nat} : ∀ {H : ThyName} {nm : LName} {i : ConstInfo},
    homeInfoB L k H nm = some i → homeInfo L H nm = some i
  | H, .base n, i, h => by simpa [homeInfoB, homeInfo] using h
  | H, .sub s S0 orig, i, h => by
    unfold homeInfoB at h
    split at h
    · rename_i hc
      rw [structMorB_eq hc] at h
      unfold homeInfo
      cases hs : (L H).bind (·.structLookup s) with
      | none => rw [hs] at h; cases h
      | some p =>
        obtain ⟨Sdom, as⟩ := p
        rw [hs] at h
        simp only at h ⊢
        split at h
        · rename_i hv
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv
          have h1 : Visible L Sdom S0 := visDec_sound hv.1
          have h2 : ¬ Visible L H S0 := fun hvis => by
            rw [(visDec_iff hc).mpr hvis] at hv; exact Bool.noConfusion hv.2
          have hc' : Visible L Sdom S0 ∧ ¬ Visible L H S0 := ⟨h1, h2⟩
          simp only [hc', and_self, not_false_eq_true, ↓reduceIte]
          obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [homeInfoB_sound hj]
          rfl
        · cases h
    · cases h

/-- Computable flattening, including structure copies. -/
def flatB (L : Library) (n : Nat) (T : ThyName) : Sig := fun c =>
  if visDec L n T c.thy then homeInfoB L n c.thy c.name else none

theorem flatB_sub (L : Library) (n : Nat) (T : ThyName) : (flatB L n T).Sub (flat L T) := by
  intro c i h
  unfold flatB at h
  split at h
  · rename_i hv
    exact flat_eq_some.mpr ⟨visDec_sound hv, homeInfoB_sound h⟩
  · cases h

/-- With completeness certificates, the computable flattening is exact. -/
theorem flatB_eq {L : Library} {n : Nat} {T : ThyName} (c : GName)
    (hT : closedUnderEdges L (reach L n T) = true)
    (hall : ∀ H, closedUnderEdges L (reach L n H) = true) :
    flatB L n T c = flat L T c := by
  have hinfo : ∀ (H : ThyName) (nm : LName), homeInfoB L n H nm = homeInfo L H nm := by
    intro H nm
    induction nm generalizing H with
    | base m => simp [homeInfoB, homeInfo]
    | sub s S0 o ih =>
      simp only [homeInfoB, hall H, ↓reduceIte, homeInfo, structMorB_eq (hall H), ih]
      cases (L H).bind (·.structLookup s) with
      | none => rfl
      | some p =>
        obtain ⟨Sdom, as⟩ := p
        simp only
        have e1 := @visDec_iff L n Sdom S0 (hall Sdom)
        have e2 := @visDec_iff L n H S0 (hall H)
        by_cases h1 : Visible L Sdom S0 <;> by_cases h2 : Visible L H S0 <;>
          simp_all
  unfold flatB flat
  rw [hinfo]
  by_cases hv : Visible L T c.thy
  · simp [hv, (visDec_iff hT).mpr hv]
  · have : visDec L n T c.thy = false := by
      cases e : visDec L n T c.thy
      · rfl
      · exact absurd ((visDec_iff hT).mp e) hv
    simp [hv, this]

/-! ## Checking a view -/

/-- The theory declares no structures. -/
def noStructs (th : Theory) : Bool := th.decls.all fun | .struct .. => false | _ => true

/-- The term mentions no constant of theory `D`. -/
def avoids (D : ThyName) : Term → Bool
  | .var _ => true
  | .const c => c.thy != D
  | .app f a => avoids D f && avoids D a
  | .bind b A t => avoids D b && avoids D A && avoids D t

theorem avoids_sound : ∀ {D : ThyName} {t : Term}, avoids D t = true →
    t.UsesOnly fun c => c.thy ≠ D
  | _, .var _, _ => trivial
  | D, .const c, h => by simpa [avoids, Term.UsesOnly] using h
  | D, .app f a, h => by
    simp only [avoids, Bool.and_eq_true] at h
    exact ⟨avoids_sound h.1, avoids_sound h.2⟩
  | D, .bind b A t, h => by
    simp only [avoids, Bool.and_eq_true] at h
    exact ⟨avoids_sound h.1.1, avoids_sound h.1.2, avoids_sound h.2⟩

def optAll (p : Term → Bool) : Option Term → Bool
  | some t => p t
  | none => true

/-- Check one local constant `n` of the domain against its assignment. -/
def checkConst (L : Library) (k : Nat) (v : View) (th : Theory) (n : String) : Bool :=
  match th.localLookup n with
  | some ⟨some A, d⟩ =>
    LF.Checker.typeCheck (flatB L k v.cod) [] (v.toSubst ⟨v.dom, n⟩) (A.trans v.toSubst) &&
    optAll (fun e => LF.Checker.eqCheck (flatB L k v.cod) [] (v.toSubst ⟨v.dom, n⟩)
      (e.trans v.toSubst) (A.trans v.toSubst)) d
  | some ⟨none, _⟩ => true
  | none => true

/-- Check a theory other than the domain that is visible from it: it must also be visible
from the codomain, and its declarations must not mention the domain. -/
def checkShared (L : Library) (k : Nat) (v : View) (R : ThyName) : Bool :=
  R == v.dom || (visibleB L k v.cod R &&
    match L R with
    | some th => th.decls.all fun
        | .const _ tp df => optAll (avoids v.dom) tp && optAll (avoids v.dom) df
        | _ => true
    | none => true)

/-- **The view checker.** `k` bounds the searches. -/
def checkView (L : Library) (k : Nat) (v : View) : Bool :=
  let Ls := reach L k v.dom
  closedUnderEdges L Ls &&
  Ls.all (fun R => match L R with | some th => noStructs th | none => true) &&
  v.dom != LF.thy &&
  v.assign.all (fun p => closedB 0 p.2) &&
  (match L v.dom with
   | some th => th.decls.all fun | .const n _ _ => checkConst L k v th n | _ => true
   | none => true) &&
  Ls.all (checkShared L k v)

/-! ## Soundness -/

theorem localLookup_mem {th : Theory} {n : String} {i : ConstInfo}
    (h : th.localLookup n = some i) : Decl.const n i.tp i.df ∈ th.decls := by
  unfold Theory.localLookup at h
  obtain ⟨d, hd, hds⟩ := List.exists_of_findSome?_eq_some h
  cases d with
  | const n' tp df =>
    simp only at hds
    split at hds
    · subst_vars; cases hds; exact hd
    · cases hds
  | incl => cases hds
  | struct => cases hds

theorem homeInfo_base_of_noStructs {L : Library} {R : ThyName} {th : Theory} (hR : L R = some th)
    (hns : noStructs th = true) {nm : LName} {i : ConstInfo} (h : homeInfo L R nm = some i) :
    ∃ m, nm = .base m ∧ th.localLookup m = some i := by
  cases nm with
  | base m => exact ⟨m, rfl, by simpa [homeInfo, hR] using h⟩
  | sub s S0 o =>
    exfalso
    have hsl : th.structLookup s = none := by
      unfold Theory.structLookup
      rw [List.findSome?_eq_none_iff]
      intro d hd
      simp only [noStructs, List.all_eq_true] at hns
      have := hns d hd
      cases d with
      | struct => simp at this
      | _ => rfl
    simp [homeInfo, hR, hsl] at h

theorem homeInfo_none {L : Library} {R : ThyName} (h : L R = none) (nm : LName) :
    homeInfo L R nm = none := by
  cases nm <;> simp [homeInfo, h]

theorem trans_avoids {v : View} {t : Term} (h : avoids v.dom t = true) :
    t.trans v.toSubst = t := by
  rw [Term.trans_congr (avoids_sound h) (τ := Subst.id) (fun c hc => View.toSubst_other hc),
    Term.trans_id]

/-- **Soundness of the view checker.** -/
theorem checkView_sound {L : Library} {k : Nat} {v : View} (h : checkView L k v = true) :
    v.WellTyped LF.foundation L := by
  simp only [checkView, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hcl, hns⟩, hlf⟩, hasg⟩, hloc⟩, hsh⟩ := h
  have hcl' := closedUnderEdges_sound hcl
  have hdom : v.dom ∈ reach L k v.dom := self_mem_reach L k v.dom
  -- the domain's theories have no structures
  have noS : ∀ R, Visible L v.dom R → ∀ th, L R = some th → noStructs th = true := by
    intro R hv th hth
    have := hns R (visible_mem_of_closed hcl' hdom hv)
    rw [hth] at this; exact this
  apply View.isMorphism_of_check
  · intro p hp; exact closedB_sound (hasg p hp)
  · intro c hc
    simp only [LF.foundation] at hc
    rw [hc]; exact Ne.symm hlf
  · intro n A d hfl
    obtain ⟨-, hhi⟩ := flat_eq_some.mp hfl
    cases hth : L v.dom with
    | none => rw [homeInfo_none hth] at hhi; cases hhi
    | some th =>
      obtain ⟨m, hm, hll⟩ := homeInfo_base_of_noStructs hth (noS _ (.refl _) th hth) hhi
      subst hm
      rw [hth] at hloc
      simp only [List.all_eq_true] at hloc
      have := hloc _ (localLookup_mem hll)
      simp only [checkConst, hll, Bool.and_eq_true] at this
      obtain ⟨hty, hdf⟩ := this
      refine ⟨(LF.Checker.check_sound hty).mono (flatB_sub L k v.cod), ?_⟩
      intro e he
      subst he
      exact (LF.Checker.eq_sound hdf).mono (flatB_sub L k v.cod)
  · intro c i hne hfl
    obtain ⟨hv, hhi⟩ := flat_eq_some.mp hfl
    have hmem := visible_mem_of_closed hcl' hdom hv
    have := hsh c.thy hmem
    simp only [checkShared, Bool.or_eq_true, beq_iff_eq, hne, false_or,
      Bool.and_eq_true] at this
    obtain ⟨hvc, hdecls⟩ := this
    refine ⟨flat_eq_some.mpr ⟨visibleB_sound hvc, hhi⟩, ?_⟩
    cases hth : L c.thy with
    | none => rw [homeInfo_none hth] at hhi; cases hhi
    | some th =>
      obtain ⟨m, -, hll⟩ := homeInfo_base_of_noStructs hth (noS _ hv th hth) hhi
      rw [hth] at hdecls
      simp only [List.all_eq_true] at hdecls
      have := hdecls _ (localLookup_mem hll)
      simp only [Bool.and_eq_true] at this
      obtain ⟨htp, hdf⟩ := this
      refine ⟨fun A hA => ?_, fun e he => ?_⟩
      · rw [hA] at htp; exact trans_avoids htp
      · rw [he] at hdf; exact trans_avoids hdf

/-! ## Checking theories -/

/-- The library in which theory `T` only has the declarations `ds` (a prefix of its body). -/
def setDecls (L : Library) (T : ThyName) (ds : List Decl) : Library := fun R =>
  if R = T then (L T).map fun th => { th with decls := ds } else L R

/-- A declaration is well-formed over `S`: the type of a constant is a type or a kind, and
its definiens has that type. -/
def DeclOK (S : Sig) : Decl → Prop
  | .const _ (some A) df =>
    (Derivable LF.foundation S (.typing [] A LF.type) ∨
      Derivable LF.foundation S (.typing [] A LF.kind)) ∧
    ∀ e, df = some e → Derivable LF.foundation S (.typing [] e A)
  | _ => True

/-- A theory is well-formed if each declaration is well-formed over the theory up to it. -/
def TheoryWF (L : Library) (T : ThyName) : Prop :=
  ∀ th, L T = some th → ∀ k d, th.decls[k]? = some d →
    DeclOK (flat (setDecls L T (th.decls.take k)) T) d

/-- Check one declaration over a signature. -/
def checkDecl (S : Sig) : Decl → Bool
  | .const _ (some A) df =>
    (LF.Checker.typeCheck S [] A LF.type || LF.Checker.typeCheck S [] A LF.kind) &&
    optAll (fun e => LF.Checker.typeCheck S [] e A) df
  | _ => true

/-- **The theory checker**, as MMT checks a theory declaration by declaration. -/
def checkTheory (L : Library) (k : Nat) (T : ThyName) : Bool :=
  match L T with
  | some th => (List.range th.decls.length).all fun i =>
      match th.decls[i]? with
      | some d => checkDecl (flatB (setDecls L T (th.decls.take i)) k T) d
      | none => true
  | none => true

theorem checkDecl_sound {S S' : Sig} (hSS : S.Sub S') {d : Decl} (h : checkDecl S d = true) :
    DeclOK S' d := by
  cases d with
  | const n tp df =>
    cases tp with
    | none => trivial
    | some A =>
      simp only [checkDecl, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hA, hdf⟩ := h
      refine ⟨?_, fun e he => ?_⟩
      · rcases hA with hA | hA
        · exact .inl ((LF.Checker.check_sound hA).mono hSS)
        · exact .inr ((LF.Checker.check_sound hA).mono hSS)
      · subst he
        exact (LF.Checker.check_sound hdf).mono hSS
  | incl => trivial
  | struct => trivial

/-- **Soundness of the theory checker.** -/
theorem checkTheory_sound {L : Library} {k : Nat} {T : ThyName} (h : checkTheory L k T = true) :
    TheoryWF L T := by
  intro th hth i d hd
  unfold checkTheory at h
  rw [hth] at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hi : i < th.decls.length := by
    rcases Nat.lt_or_ge i th.decls.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hd; cases hd
  have := h i hi
  rw [hd] at this
  exact checkDecl_sound (flatB_sub _ k T) this

/-- Well-typed declarations are closed: a consequence of scoping. -/
theorem DeclOK.closed {S : Sig}
    (hS : ∀ c A d, S c = some ⟨some A, d⟩ → A.ClosedAt 0 ∧ ∀ e, d = some e → e.ClosedAt 0)
    {n : String} {A : Term} {df : Option Term} (h : DeclOK S (.const n (some A) df)) :
    A.ClosedAt 0 ∧ ∀ e, df = some e → e.ClosedAt 0 := by
  refine ⟨?_, fun e he => (LF.scoping hS (h.2 e he) trivial).1⟩
  rcases h.1 with h | h
  · exact (LF.scoping hS h trivial).1
  · exact (LF.scoping hS h trivial).1

end MMT
