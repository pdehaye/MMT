import MMTlib.Core.Judgment

/-!
# Pushouts and structures

MMT's `structure` declarations (`api/symbols/Structure.scala`) and the pushout
operator on theory diagrams (`api/modules/diagrams/PushoutOperator.scala`) both rest on
one construction: the pushout of a theory extension `S ⊆ S'` along a morphism `σ : S → T`.

```
   S  ──σ──▶  T
   │          │ incl
   ▼          ▼
   S' ──σ'──▶ T'      T' = T + (S' \ S) translated along σ'
```

The constants of `S'` that are not in `S` are copied into `T'` under fresh names
given by a renaming `ρ`. MMT forms these names as `T?s/c` for a structure `s`. Their
types and definitions are translated along `σ'`, and `σ'` sends `c ↦ ρ c` on new
constants and `c ↦ σ c` on old ones. Optional *assignments* give definitions to new
constants that have none. These are the assignments of a structure. With
assignments, the universal property needs one more hypothesis: the mediating
morphism must respect them.

Main results:
* `pushout_incl`: `T ⊆ T'`.
* `pushout_isMorphism`: `σ' : S' → T'` is a well-typed morphism.
* `pushout_commutes`: `σ'` agrees with `σ` on `S`, so the square commutes.
* `pushout_universal`: for every cocone `τ : T → U`, `μ : S' → U` there is a mediating
  morphism `T' → U`. It is unique on the constants of `T'`.
* `Structure.isMorphism`: a structure, i.e. the pushout of the meta-theory inclusion
  `M ⊆ S` along `M ⊆ T`, induces a well-typed morphism `S → T'`.
-/

namespace MMT

/-- `c` is declared in `S`. -/
def Sig.Has (S : Sig) (c : GName) : Prop := (S c).isSome = true

/-- A signature is closed if the types and definitions of its constants only refer to
its own constants. Flattenings of well-formed MMT theories are closed. -/
def Sig.Closed (S : Sig) : Prop :=
  ∀ c i, S c = some i → (∀ A, i.tp = some A → A.UsesOnly S.Has) ∧
    (∀ e, i.df = some e → e.UsesOnly S.Has)

/-- `σ` maps the constants of `S` to terms over `T`. -/
def Subst.LandsIn (σ : Subst) (S T : Sig) : Prop := ∀ c, S.Has c → (σ c).UsesOnly T.Has

/-- An injective renaming of constants with a partial inverse. It is used to pick fresh
names for the copied constants (MMT: `c ↦ T?s/c`). -/
structure Renaming where
  fwd : GName → GName
  bwd : GName → Option GName
  bwd_fwd : ∀ c, bwd (fwd c) = some c
  fwd_bwd : ∀ c d, bwd d = some c → fwd c = d

/-! ## The construction -/

section Construction

variable (S S' T : Sig) (σ : Subst) (ρ : Renaming) (a : GName → Option Term)

/-- `c` is a constant of the extension that is not in the shared part. -/
def isNew (c : GName) : Bool := (S c).isNone && (S' c).isSome

/-- The morphism `σ' : S' → T'`. -/
def poMor : Subst := fun c => if isNew S S' c then .const (ρ.fwd c) else σ c

/-- The declaration of the copy of a new constant `c` in `T'`. -/
def poInfo (c : GName) (i : ConstInfo) : ConstInfo :=
  ⟨i.tp.map (·.trans (poMor S S' σ ρ)), (a c).or (i.df.map (·.trans (poMor S S' σ ρ)))⟩

/-- The pushout signature `T'`. -/
def poSig : Sig := fun d =>
  match T d with
  | some i => some i
  | none =>
    match ρ.bwd d with
    | some c => if isNew S S' c then (S' c).map (poInfo S S' σ ρ a c) else none
    | none => none

end Construction

/-- Side conditions of the pushout. -/
structure PushoutHyp (F : Foundation) (S S' T : Sig) (σ : Subst) (ρ : Renaming)
    (a : GName → Option Term) : Prop where
  sub      : S.Sub S'
  mor      : IsMorphism F S T σ
  closedS  : S.Closed
  fresh    : ∀ c, T (ρ.fwd c) = none
  metaNew  : ∀ c, isNew S S' c = true → ¬ F.metaSym c
  metaFwd  : ∀ c, ¬ F.metaSym (ρ.fwd c)
  assignOk : ∀ c t, a c = some t → isNew S S' c = true ∧ ∃ A, S' c = some ⟨some A, none⟩

section Lemmas

variable {F : Foundation} {S S' T : Sig} {σ : Subst} {ρ : Renaming} {a : GName → Option Term}

theorem isNew_false_has {c : GName} (hS' : S'.Has c)
    (hn : isNew S S' c = false) : S.Has c := by
  unfold isNew at hn; unfold Sig.Has at *
  cases hc : S c <;> simp_all

theorem isNew_has {c : GName} (h : S.Has c) : isNew S S' c = false := by
  unfold isNew Sig.Has at *; cases hc : S c <;> simp_all

theorem poMor_old {c : GName} (h : S.Has c) : poMor S S' σ ρ c = σ c := by
  simp [poMor, isNew_has h]

theorem poSig_old {d : GName} {i : ConstInfo} (h : T d = some i) :
    poSig S S' T σ ρ a d = some i := by
  simp [poSig, h]

theorem poSig_new (hfresh : ∀ c, T (ρ.fwd c) = none) {c : GName} {i : ConstInfo}
    (hn : isNew S S' c = true) (hc : S' c = some i) :
    poSig S S' T σ ρ a (ρ.fwd c) = some (poInfo S S' σ ρ a c i) := by
  simp [poSig, hfresh, ρ.bwd_fwd, hn, hc]

theorem poSig_cases {d : GName} {i : ConstInfo} (h : poSig S S' T σ ρ a d = some i) :
    T d = some i ∨ (T d = none ∧ ∃ c j, ρ.bwd d = some c ∧ isNew S S' c = true ∧
      S' c = some j ∧ i = poInfo S S' σ ρ a c j) := by
  unfold poSig at h
  cases hT : T d with
  | some i' => simp only [hT] at h; exact .inl h
  | none =>
    simp only [hT] at h
    refine .inr ⟨rfl, ?_⟩
    cases hb : ρ.bwd d with
    | none => simp [hb] at h
    | some c =>
      simp only [hb] at h
      by_cases hn : isNew S S' c = true
      · simp only [hn, ↓reduceIte] at h
        cases hc : S' c with
        | none => simp [hc] at h
        | some j => simp [hc] at h; exact ⟨c, j, rfl, hn, hc, h.symm⟩
      · simp [hn] at h

end Lemmas

/-! ## The pushout square -/

section Square

variable {F : Foundation} {S S' T : Sig} {σ : Subst} {ρ : Renaming} {a : GName → Option Term}

/-- `T` is included in the pushout. -/
theorem pushout_incl : T.Sub (poSig S S' T σ ρ a) := fun _ _ h => poSig_old h

/-- The square commutes: `σ'` restricted to `S` is `σ`. -/
theorem pushout_commutes {c : GName} (h : S.Has c) : poMor S S' σ ρ c = σ c := poMor_old h

/-- `σ'` agrees with `σ` on the types and definitions of `S`. -/
theorem trans_poMor_old (hp : PushoutHyp F S S' T σ ρ a) {c : GName} {i : ConstInfo}
    (hc : S c = some i) :
    (∀ A, i.tp = some A → A.trans (poMor S S' σ ρ) = A.trans σ) ∧
    (∀ e, i.df = some e → e.trans (poMor S S' σ ρ) = e.trans σ) :=
  ⟨fun A hA => Term.trans_congr ((hp.closedS c i hc).1 A hA) (fun _ h => poMor_old h),
   fun e he => Term.trans_congr ((hp.closedS c i hc).2 e he) (fun _ h => poMor_old h)⟩

/-- `σ' : S' → T'` is a well-typed morphism. -/
theorem pushout_isMorphism (hp : PushoutHyp F S S' T σ ρ a) :
    IsMorphism F S' (poSig S S' T σ ρ a) (poMor S S' σ ρ) where
  closed c := by
    unfold poMor; split
    · trivial
    · exact hp.mor.closed c
  fixMeta c hc := by
    have : isNew S S' c = false := by
      cases h : isNew S S' c
      · rfl
      · exact absurd hc (hp.metaNew c h)
    simp [poMor, this, hp.mor.fixMeta c hc]
  typed {c A d} hc := by
    cases hn : isNew S S' c
    · have hS : S.Has c := isNew_false_has (by simp [Sig.Has, hc]) hn
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hS
      have hi' : i = ⟨some A, d⟩ := by have := hp.sub _ _ hi; rw [hc] at this; cases this; rfl
      subst hi'
      rw [poMor_old hS, (trans_poMor_old hp hi).1 A rfl]
      exact (hp.mor.typed hi).mono pushout_incl
    · simp only [poMor, hn, ↓reduceIte]
      exact .const (d := (poInfo S S' σ ρ a c ⟨some A, d⟩).df) (poSig_new hp.fresh hn hc)
  defn {c A d} hc := by
    cases hn : isNew S S' c
    · have hS : S.Has c := isNew_false_has (by simp [Sig.Has, hc]) hn
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hS
      have hi' : i = ⟨some A, some d⟩ := by
        have := hp.sub _ _ hi; rw [hc] at this; cases this; rfl
      subst hi'
      rw [poMor_old hS, (trans_poMor_old hp hi).1 A rfl, (trans_poMor_old hp hi).2 d rfl]
      exact (hp.mor.defn hi).mono pushout_incl
    · simp only [poMor, hn, ↓reduceIte]
      have ha : a c = none := by
        cases h : a c with
        | none => rfl
        | some t =>
          obtain ⟨-, A', hA'⟩ := hp.assignOk c t h
          rw [hc] at hA'; cases hA'
      have := poSig_new (a := a) (σ := σ) hp.fresh hn hc
      simp only [poInfo, ha, Option.map_some, Option.none_or] at this
      exact .defn this

end Square

/-! ## The universal property -/

section Universal

variable {F : Foundation} {S S' T U : Sig} {σ τ μ : Subst} {ρ : Renaming}
  {a : GName → Option Term}

variable (S S' T σ τ μ ρ) in
/-- The mediating morphism `T' → U` induced by a cocone `τ : T → U`, `μ : S' → U`. -/
def poMed : Subst := fun d =>
  if (T d).isSome then τ d else
    match ρ.bwd d with
    | some c => if isNew S S' c then μ c else τ d
    | none => τ d

theorem poMed_T {d : GName} (h : T.Has d) : poMed S S' T τ μ ρ d = τ d := by
  simp only [Sig.Has] at h; simp [poMed, h]

theorem poMed_fwd (hfresh : ∀ c, T (ρ.fwd c) = none) {c : GName} (hn : isNew S S' c = true) :
    poMed S S' T τ μ ρ (ρ.fwd c) = μ c := by
  simp [poMed, hfresh, ρ.bwd_fwd, hn]

/-- `σ' ; med = μ` on the constants of `S'`. -/
theorem pushout_factor (hp : PushoutHyp F S S' T σ ρ a) (hland : σ.LandsIn S T)
    (hcomm : ∀ c, S.Has c → μ c = (σ c).trans τ) {c : GName} (hc : S'.Has c) :
    (poMor S S' σ ρ c).trans (poMed S S' T τ μ ρ) = μ c := by
  cases hn : isNew S S' c
  · have hS := isNew_false_has hc hn
    rw [poMor_old hS, hcomm c hS]
    exact Term.trans_congr (hland c hS) (fun _ h => poMed_T h)
  · simp only [poMor, hn, ↓reduceIte, Term.trans]
    exact poMed_fwd hp.fresh hn

/-- **Universal property of the pushout.** For a cocone of well-typed morphisms
`τ : T → U`, `μ : S' → U` that agree on `S` (`μ|S = σ;τ`) and respect the assignments,
the mediating map is a well-typed morphism `T' → U`. It extends `τ`, factors `μ`
through `σ'`, and is unique with these properties on the constants of `T'`. -/
theorem pushout_universal (hp : PushoutHyp F S S' T σ ρ a) (hland : σ.LandsIn S T)
    (hT : T.Closed) (hS' : S'.Closed)
    (hτ : IsMorphism F T U τ) (hμ : IsMorphism F S' U μ)
    (hcomm : ∀ c, S.Has c → μ c = (σ c).trans τ)
    (hassign : ∀ c t A, a c = some t → S' c = some ⟨some A, none⟩ →
      Derivable F U (.equal [] (μ c) (t.trans (poMed S S' T τ μ ρ)) (A.trans μ))) :
    IsMorphism F (poSig S S' T σ ρ a) U (poMed S S' T τ μ ρ) ∧
    (∀ d, T.Has d → poMed S S' T τ μ ρ d = τ d) ∧
    (∀ c, S'.Has c → (poMor S S' σ ρ c).trans (poMed S S' T τ μ ρ) = μ c) ∧
    (∀ u : Subst, (∀ d, T.Has d → u d = τ d) →
      (∀ c, S'.Has c → (poMor S S' σ ρ c).trans u = μ c) →
      ∀ d, (poSig S S' T σ ρ a).Has d → u d = poMed S S' T τ μ ρ d) := by
  -- translating `S'`-terms along `σ' ; med` is translating along `μ`
  have hfac : ∀ x : Term, x.UsesOnly S'.Has →
      (x.trans (poMor S S' σ ρ)).trans (poMed S S' T τ μ ρ) = x.trans μ := by
    intro x hx
    rw [← Term.trans_comp]
    exact Term.trans_congr hx (fun c hc => pushout_factor hp hland hcomm hc)
  have hTτ : ∀ x : Term, x.UsesOnly T.Has → x.trans (poMed S S' T τ μ ρ) = x.trans τ :=
    fun x hx => Term.trans_congr hx (fun _ h => poMed_T h)
  refine ⟨?_, fun d h => poMed_T h, fun c h => pushout_factor hp hland hcomm h, ?_⟩
  · constructor
    · intro d
      unfold poMed
      split
      · exact hτ.closed d
      · split
        · split
          · exact hμ.closed _
          · exact hτ.closed d
        · exact hτ.closed d
    · intro d hd
      unfold poMed
      split
      · exact hτ.fixMeta d hd
      · split
        · rename_i c hb
          split
          · exact absurd (ρ.fwd_bwd c d hb ▸ hd) (hp.metaFwd c)
          · exact hτ.fixMeta d hd
        · exact hτ.fixMeta d hd
    · intro d A e hd
      rcases poSig_cases hd with hd | ⟨_, c, j, hb, hn, hj, hi⟩
      · rw [poMed_T (by simp [Sig.Has, hd]), hTτ A ((hT d _ hd).1 A rfl)]
        exact hτ.typed hd
      · obtain rfl := ρ.fwd_bwd c d hb
        rw [poMed_fwd hp.fresh hn]
        obtain ⟨jt, jd⟩ := j
        simp only [poInfo, ConstInfo.mk.injEq] at hi
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hi.1.symm
        rw [hfac A' ((hS' c _ hj).1 A' hA')]
        subst hA'
        exact hμ.typed hj
    · intro d A e hd
      rcases poSig_cases hd with hd | ⟨_, c, j, hb, hn, hj, hi⟩
      · rw [poMed_T (by simp [Sig.Has, hd]), hTτ A ((hT d _ hd).1 A rfl),
          hTτ e ((hT d _ hd).2 e rfl)]
        exact hτ.defn hd
      · obtain rfl := ρ.fwd_bwd c d hb
        rw [poMed_fwd hp.fresh hn]
        obtain ⟨jt, jd⟩ := j
        simp only [poInfo, ConstInfo.mk.injEq] at hi
        obtain ⟨hA, he⟩ := hi
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hA.symm
        rw [hfac A' ((hS' c _ hj).1 A' hA')]
        subst hA'
        cases ha : a c with
        | some t =>
          obtain ⟨-, A'', hA''⟩ := hp.assignOk c t ha
          rw [hj] at hA''
          simp only [Option.some.injEq, ConstInfo.mk.injEq] at hA''
          obtain ⟨-, rfl⟩ := hA''
          rw [ha] at he
          simp at he
          subst he
          exact hassign c _ A' ha hj
        | none =>
          rw [ha] at he
          simp only [Option.none_or] at he
          obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp he.symm
          rw [hfac e' ((hS' c _ hj).2 e' he')]
          subst he'
          exact hμ.defn hj
  · intro u hu1 hu2 d hd
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hd
    rcases poSig_cases hi with hd' | ⟨hTn, c, j, hb, hn, hj, -⟩
    · have hTd : T.Has d := by simp [Sig.Has, hd']
      rw [hu1 d hTd, poMed_T hTd]
    · obtain rfl := ρ.fwd_bwd c d hb
      have := hu2 c (by simp [Sig.Has, hj])
      simp only [poMor, hn, ↓reduceIte, Term.trans] at this
      rw [this, poMed_fwd hp.fresh hn]

end Universal

/-! ## Structures -/

/-- An MMT structure `structure s : S = {assign}` declared in a theory with signature `T`.
`M` is the meta-theory shared by `S` and `T`. The constants of `S` outside `M` are
copied into the host under the renaming `ρ` (MMT: `c ↦ T?s/c`). Assignments define
copied constants that were undefined. -/
structure Structure where
  M      : Sig
  S      : Sig
  T      : Sig
  ρ      : Renaming
  assign : GName → Option Term

namespace Structure

variable (s : Structure)

/-- The host theory after elaborating the structure. -/
def host : Sig := poSig s.M s.S s.T Subst.id s.ρ s.assign

/-- The morphism `S → host` induced by the structure. -/
def mor : Subst := poMor s.M s.S Subst.id s.ρ

/-- Well-formedness conditions for a structure. -/
structure WF (F : Foundation) : Prop where
  metaS    : s.M.Sub s.S
  metaT    : s.M.Sub s.T
  closedM  : s.M.Closed
  fresh    : ∀ c, s.T (s.ρ.fwd c) = none
  metaNew  : ∀ c, isNew s.M s.S c = true → ¬ F.metaSym c
  metaFwd  : ∀ c, ¬ F.metaSym (s.ρ.fwd c)
  assignOk : ∀ c t, s.assign c = some t →
    isNew s.M s.S c = true ∧ ∃ A, s.S c = some ⟨some A, none⟩

theorem WF.pushoutHyp {F : Foundation} {s : Structure} (h : s.WF F) :
    PushoutHyp F s.M s.S s.T Subst.id s.ρ s.assign where
  sub := h.metaS
  mor := IsMorphism.incl h.metaT
  closedS := h.closedM
  fresh := h.fresh
  metaNew := h.metaNew
  metaFwd := h.metaFwd
  assignOk := h.assignOk

/-- A structure induces a well-typed morphism from the imported theory into the host. -/
theorem isMorphism {F : Foundation} {s : Structure} (h : s.WF F) :
    IsMorphism F s.S s.host s.mor :=
  pushout_isMorphism h.pushoutHyp

/-- The host's original declarations are kept. -/
theorem host_incl (s : Structure) : s.T.Sub s.host := pushout_incl

/-- The meta-theory is translated identically. -/
theorem mor_meta (s : Structure) {c : GName} (h : s.M.Has c) : s.mor c = .const c :=
  pushout_commutes h

/-- Everything derivable in the imported theory is derivable in the host, after
renaming. -/
theorem preserves {F : Foundation} {s : Structure} (h : s.WF F) {J : Judgment}
    (hJ : Derivable F s.S J) : Derivable F s.host (J.trans s.mor) :=
  Derivable.trans (s.isMorphism h) hJ

end Structure

end MMT
