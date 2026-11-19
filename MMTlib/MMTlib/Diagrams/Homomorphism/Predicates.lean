import MMTlib.Diagrams.Homomorphism.Basic

/-!
# The homomorphism functor with predicates

Extends `Hom(Σ)` to first-order signatures with *predicate symbols* `p : a₁ … aₙ`. For
each predicate, `Hom(Σ)` declares the two copies and the condition that homomorphisms
preserve it:

```
  p¹ : a₁¹ → … → aₙ¹ → prop,   p² : a₁² → … → aₙ² → prop,
  p^h : Π x₁:a₁¹ … xₙ:aₙ¹. ded (p¹ x₁ … xₙ) → ded (p² (h_{a₁} x₁) … (h_{aₙ} xₙ))
```

The extension is conservative: the theory `homSigP` contains `homSig`
(`homSig_sub_homSigP`), so all typing results for sorts and operations carry over.

Main results:
* `predAx_typed`, `homSigP_wf`: every declaration of `Hom(Σ)` with predicates is
  well-typed;
* `FOMorP.hom_isMorphism`: signature morphisms that map predicates to predicates with
  matching profiles induce well-typed morphisms `Hom(Σ) → Hom(Σ')`;
* `FOMorP.hom_comp`: functoriality.
-/

namespace MMT.Hom

open LF Term Judgment

/-- Predicate symbols over a first-order signature, with their argument sorts. -/
structure Preds (Sg : FOSig) where
  /-- Predicates by name, with their argument sorts. -/
  pred? : String → Option (List String)
  /-- Predicate names are not sorts. -/
  not_sort : ∀ n as, pred? n = some as → Sg.isSort n = false
  /-- Predicate names are not operations. -/
  not_op : ∀ n as, pred? n = some as → Sg.op? n = none
  /-- Argument sorts are sorts. -/
  sorts : ∀ n as, pred? n = some as → ∀ a ∈ as, Sg.isSort a = true

variable (H : ThyName)

/-- The preservation axiom for a predicate `p : as`. -/
def predAx (Sg : FOSig) (p : String) (as : List String) : Term :=
  arrows (as.map (cs H "1" Sg))
    (Pi (ded (apps (cs H "1" Sg p) (args as)))
      (ded (apps (cs H "2" Sg p) ((hargs H Sg as).map (liftN 1 0)))))

/-- The declarations of the copies of a predicate. -/
def predInfo (Sg : FOSig) (P : Preds Sg) (k n : String) : Option ConstInfo :=
  (P.pred? n).bind fun as =>
    if k = "1" ∨ k = "2" then some ⟨some (arrows (as.map (cs H k Sg)) prop), none⟩
    else if k = "h" then some ⟨some (predAx H Sg n as), none⟩
    else none

/-- `Hom(Σ)` for a signature with predicates. -/
def homSigP (Sg : FOSig) (P : Preds Sg) : Sig := fun d =>
  if d.thy = H then
    match d.name with
    | .sub k thy (.base n) =>
      if thy = Sg.thy then (predInfo H Sg P k n).or (homInfo H Sg k n) else none
    | _ => none
  else metaSig d

variable {H}

theorem predInfo_none {Sg : FOSig} {P : Preds Sg} {k n : String} (h : P.pred? n = none) :
    predInfo H Sg P k n = none := by simp [predInfo, h]

theorem homInfo_pred_none {Sg : FOSig} {P : Preds Sg} {k n : String} {as : List String}
    (h : P.pred? n = some as) : homInfo H Sg k n = none := by
  simp [homInfo, P.not_sort n as h, P.not_op n as h]

theorem homSigP_cp {Sg : FOSig} {P : Preds Sg} {k n : String} :
    homSigP H Sg P (cp H k Sg n) = (predInfo H Sg P k n).or (homInfo H Sg k n) := by
  simp [homSigP, cp]

theorem homSigP_meta {Sg : FOSig} {P : Preds Sg} {c : GName} (h : c.thy ≠ H) :
    homSigP H Sg P c = metaSig c := by simp [homSigP, h]

/-- The extension is conservative. -/
theorem homSig_sub_homSigP {Sg : FOSig} (P : Preds Sg) : (homSig H Sg).Sub (homSigP H Sg P) := by
  intro c i h
  rcases homSig_cases h with ⟨k, n, rfl, hi⟩ | ⟨hne, hm⟩
  · rw [homSigP_cp]
    cases hp : P.pred? n with
    | none => rw [predInfo_none hp]; simpa using hi
    | some as => rw [homInfo_pred_none hp] at hi; cases hi
  · rw [homSigP_meta hne]; exact hm

theorem homSigP_cases {Sg : FOSig} {P : Preds Sg} {c : GName} {i : ConstInfo}
    (h : homSigP H Sg P c = some i) :
    (∃ k n as, c = cp H k Sg n ∧ P.pred? n = some as ∧ predInfo H Sg P k n = some i) ∨
    homSig H Sg c = some i := by
  obtain ⟨t, nm⟩ := c
  unfold homSigP at h
  by_cases ht : t = H
  · subst ht
    simp only [↓reduceIte] at h
    split at h
    · rename_i k thy n
      split at h
      · subst_vars
        cases hp : P.pred? n with
        | none =>
          rw [predInfo_none hp] at h
          refine .inr ?_
          show homSig _ Sg (cp _ k Sg n) = some i
          rw [homSig_cp]; simpa using h
        | some as =>
          rw [homInfo_pred_none hp] at h
          exact .inl ⟨k, n, as, rfl, hp, by simpa using h⟩
      · cases h
    · cases h
  · simp only [ht, ↓reduceIte] at h
    exact .inr (by rw [homSig_meta ht]; exact h)

theorem homSigP_df {Sg : FOSig} {P : Preds Sg} {c : GName} {i : ConstInfo}
    (h : homSigP H Sg P c = some i) : i.df = none := by
  rcases homSigP_cases h with ⟨k, n, as, -, hp, hi⟩ | h
  · unfold predInfo at hi
    rw [hp] at hi
    simp only [Option.bind_some] at hi
    repeat' split at hi
    all_goals (cases hi <;> rfl)
  · exact homSig_df h

/-! ## Well-typedness -/

section WF

variable {Sg : FOSig} {P : Preds Sg}

theorem Args.mono {S S' : Sig} (hSS : S.Sub S') {Γ : Ctx} {xs As : List Term}
    (h : Args S Γ xs As) : Args S' Γ xs As := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hx.mono hSS) ih

/-- Typings in `Hom(Σ)` without predicates carry over. -/
theorem lift_typed {J : Judgment} (h : D (homSig H Sg) J) : D (homSigP H Sg P) J :=
  h.mono (homSig_sub_homSigP P)

theorem pred_typed {k p : String} {as : List String} (hk : k = "1" ∨ k = "2")
    (hp : P.pred? p = some as) (Γ : Ctx) :
    D (homSigP H Sg P) (.typing Γ (cs H k Sg p) (arrows (as.map (cs H k Sg)) prop)) :=
  .const (c := cp H k Sg p) (d := none) (by rw [homSigP_cp]; simp [predInfo, hp, hk])

/-- The arguments `h(x₁) … h(xₙ)`, shifted under one more binder. -/
theorem hargs_lift_typed (as : List String) (has : ∀ a ∈ as, Sg.isSort a = true) (B : Term)
    (Γ₀ : Ctx) :
    Args (homSigP H Sg P) (B :: ((as.map (cs H "1" Sg)).reverse ++ Γ₀))
      ((hargs H Sg as).map (liftN 1 0)) (as.map (cs H "2" Sg)) := by
  induction as generalizing Γ₀ with
  | nil => exact .nil
  | cons a rest ih =>
    have hv : (B :: ((rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀)))[rest.length + 1]? =
        some (cs H "1" Sg a) := by
      rw [List.getElem?_cons_succ, List.getElem?_append_right (by simp)]; simp
    have hx : D (homSigP H Sg P) (.typing _ (.var (rest.length + 1)) (cs H "1" Sg a)) :=
      r0 (LF.Rule.var _ (rest.length + 1) _ hv)
    have happ : D (homSigP H Sg P) (.typing _ (.app (cs H "h" Sg a) (.var (rest.length + 1)))
        (cs H "2" Sg a)) :=
      r2 (LF.Rule.appE _ _ _ _ _) (lift_typed (hom_typed (has a (by simp)) _)) hx
    have e : ((a :: rest).map (cs H "1" Sg)).reverse ++ Γ₀ =
        (rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀) := by simp
    rw [e]
    exact .cons happ (ih (fun x hx => has x (by simp [hx])) (cs H "1" Sg a :: Γ₀))

variable (hH : H ≠ sfol)
include hH

theorem metaP_typed {c : GName} {A : Term} {d : Option Term} (h : metaSig c = some ⟨some A, d⟩)
    (Γ : Ctx) : D (homSigP H Sg P) (.typing Γ (.const c) A) :=
  .const (by rw [homSigP_meta (by rw [metaSig_thy h]; exact Ne.symm hH)]; exact h)

theorem prop_typed (Γ : Ctx) : D (homSigP H Sg P) (.typing Γ prop type) :=
  metaP_typed hH (d := none) (by simp [metaSig, propN]) Γ

theorem ded_typed {Γ : Ctx} {p : Term} (hp : D (homSigP H Sg P) (.typing Γ p prop)) :
    D (homSigP H Sg P) (.typing Γ (ded p) type) :=
  r2 (LF.Rule.appE Γ prop type (.const dedN) p)
    (metaP_typed hH (d := none) (by simp [metaSig, propN, dedN]) Γ) hp

/-- **Each predicate-preservation axiom is well-typed.** -/
theorem predAx_typed {p : String} {as : List String} (hp : P.pred? p = some as) :
    D (homSigP H Sg P) (.typing [] (predAx H Sg p as) type) := by
  have has := P.sorts p as hp
  have hcl : ∀ k, ∀ a ∈ as.map (cs H k Sg), a.ClosedAt 0 := by
    intro k a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial
  apply arrows_typed
  · intro a ha Γ'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact lift_typed (sort_typed (.inl rfl) (has x hx) Γ')
  · simp only [List.append_nil]
    have hP1 : D (homSigP H Sg P) (.typing (as.map (cs H "1" Sg)).reverse
        (apps (cs H "1" Sg p) (args as)) prop) := by
      have hargs : Args (homSigP H Sg P) ((as.map (cs H "1" Sg)).reverse) (args as)
          (as.map (cs H "1" Sg)) := by
        have := args_typed (H := H) (Sg := Sg) (cs H "1" Sg) (fun a => ⟨_, rfl⟩) as []
        simp only [List.append_nil] at this
        exact this.mono (homSig_sub_homSigP P)
      exact apps_typed (pred_typed (.inl rfl) hp _) hargs (hcl "1") trivial
    have hl := hargs_lift_typed (H := H) (P := P) as has (ded (apps (cs H "1" Sg p) (args as))) []
    simp only [List.append_nil] at hl
    have hP2 : D (homSigP H Sg P) (.typing
        (ded (apps (cs H "1" Sg p) (args as)) :: (as.map (cs H "1" Sg)).reverse)
        (apps (cs H "2" Sg p) ((hargs H Sg as).map (liftN 1 0))) prop) :=
      apps_typed (pred_typed (.inr rfl) hp _) hl (hcl "2") trivial
    exact r2 (LF.Rule.piType _ _ _) (ded_typed hH hP1) (ded_typed hH hP2)

/-- **`Hom(Σ)` with predicates is well-formed.** -/
theorem homSigP_wf {k n : String} {A : Term} {d : Option Term}
    (h : homSigP H Sg P (cp H k Sg n) = some ⟨some A, d⟩) :
    A = type ∨ D (homSigP H Sg P) (.typing [] A type) := by
  rcases homSigP_cases h with ⟨k', n', as, he, hp, hi⟩ | h'
  · simp only [cp, GName.mk.injEq, LName.sub.injEq, LName.base.injEq, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    unfold predInfo at hi
    rw [hp] at hi
    simp only [Option.bind_some] at hi
    by_cases hk : k = "1" ∨ k = "2"
    · simp only [hk, ↓reduceIte, Option.some.injEq, ConstInfo.mk.injEq] at hi
      obtain ⟨rfl, -⟩ := hi
      refine .inr (arrows_typed ?_ (prop_typed hH _))
      intro a ha Γ'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact lift_typed (sort_typed hk (P.sorts n as hp x hx) Γ')
    · simp only [hk, ↓reduceIte] at hi
      split at hi
      · simp only [Option.some.injEq, ConstInfo.mk.injEq] at hi
        obtain ⟨rfl, -⟩ := hi
        exact .inr (predAx_typed hH hp)
      · cases hi
  · rcases homSig_wf hH h' with h'' | h''
    · exact .inl h''
    · exact .inr (lift_typed h'')

end WF

/-! ## Signature morphisms with predicates -/

/-- A signature morphism that also maps predicates to predicates of the same profile. -/
structure FOMorP {Sg Sg' : FOSig} (P : Preds Sg) (P' : Preds Sg') extends FOMor Sg Sg' where
  /-- Predicates are mapped to predicates of the mapped profile. -/
  pred : ∀ n as, P.pred? n = some as → P'.pred? (φ n) = some (as.map φ)

namespace FOMorP

variable {Sg Sg' : FOSig} {P : Preds Sg} {P' : Preds Sg'} (μ : FOMorP P P') {H H' : ThyName}

theorem hom_closed : (μ.hom H H').Closed := by
  intro d; unfold FOMor.hom; repeat (first | split | trivial)

theorem hom_predAx (hH : H ≠ sfol) (hL : H ≠ LF.thy) (p : String) (as : List String) :
    (predAx H Sg p as).trans (μ.hom H H') = predAx H' Sg' (μ.φ p) (as.map μ.φ) := by
  have hP : μ.hom H H' piN = .const piN := FOMor.hom_fix hH hL (.inr rfl)
  have hD : μ.hom H H' dedN = .const dedN := FOMor.hom_fix hH hL (.inl rfl)
  have hargs_eq : ∀ l : List String, args (l.map μ.φ) = args l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [args, ih]
  have hargs_tr : ∀ l : List String, (args l).map (·.trans (μ.hom H H')) = args l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [args, ih, Term.trans]
  have hh_tr : ∀ l : List String,
      (hargs H Sg l).map (fun x => (liftN 1 0 x).trans (μ.hom H H')) =
      (hargs H' Sg' (l.map μ.φ)).map (liftN 1 0) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [hargs, List.map_cons]
      rw [ih]
      simp [Term.trans_liftN μ.hom_closed, Term.trans, FOMor.hom_cs]
  simp only [predAx, arrows_trans hP, List.map_map, Function.comp_def, FOMor.hom_cs, Term.trans,
    ded, hD, hP, apps_trans]
  rw [hargs_tr, hh_tr, hargs_eq]

/-- **`Hom(φ)` is a well-typed morphism** between the theories of homomorphisms of
signatures with predicates. -/
theorem hom_isMorphism (hH : H ≠ sfol) (hL : H ≠ LF.thy) (hH' : H' ≠ sfol) :
    IsMorphism LF.foundation (homSigP H Sg P) (homSigP H' Sg' P') (μ.hom H H') where
  closed := μ.hom_closed
  fixMeta c hc := FOMor.hom_fix hH hL (.inr hc)
  typed {c A d} hc := by
    rcases homSigP_cases hc with ⟨k, n, as, rfl, hp, hi⟩ | h'
    · rw [FOMor.hom_cp]
      have hp' := μ.pred n as hp
      unfold predInfo at hi
      rw [hp] at hi
      simp only [Option.bind_some] at hi
      refine .const (c := cp H' k Sg' (μ.φ n)) (d := none) ?_
      rw [homSigP_cp]
      unfold predInfo
      rw [hp']
      simp only [Option.bind_some]
      by_cases hk : k = "1" ∨ k = "2"
      · simp only [hk, ↓reduceIte, Option.some.injEq, ConstInfo.mk.injEq] at hi ⊢
        obtain ⟨rfl, rfl⟩ := hi
        simp [arrows_trans (FOMor.hom_fix hH hL (.inr rfl)), FOMor.hom_cs, Term.trans,
          FOMor.hom_fix hH hL (c := propN) (.inl rfl), Function.comp_def]
      · simp only [hk, ↓reduceIte] at hi ⊢
        split at hi
        · rename_i hh
          simp only [hh, ↓reduceIte, Option.some.injEq, ConstInfo.mk.injEq] at hi ⊢
          obtain ⟨rfl, rfl⟩ := hi
          simp [μ.hom_predAx hH hL]
        · cases hi
    · exact ((μ.toFOMor.hom_isMorphism hH hL hH').typed h').mono (homSig_sub_homSigP P')
  defn {c A d} hc := by cases homSigP_df hc

/-- Functor law: composition, on the constants of `Hom(Σ)` with predicates. -/
theorem hom_comp {Sg'' : FOSig} {P'' : Preds Sg''} (ν : FOMorP P' P'') {H'' : ThyName}
    (hH' : H' ≠ sfol) {d : GName} (hd : (homSigP H Sg P d).isSome = true) :
    (μ.toFOMor.comp ν.toFOMor).hom H H'' d = ((μ.hom H H').comp (ν.hom H' H'')) d := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hd
  rcases homSigP_cases hi with ⟨k, n, as, rfl, -, -⟩ | h'
  · simp only [FOMor.hom_cp, Subst.comp, cs, Term.trans]; rfl
  · exact FOMor.hom_comp μ.toFOMor ν.toFOMor hH' (by simp [h'])

end FOMorP

end MMT.Hom
