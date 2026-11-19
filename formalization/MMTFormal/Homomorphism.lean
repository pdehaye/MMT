import MMTFormal.LF

/-!
# The homomorphism functor

The homomorphism functor of MMT's diagram operators sends a first-order signature `Σ`
(sorts and operations) to the theory `Hom(Σ)` of homomorphisms between two
`Σ`-models:

```
  s¹ : type,  s² : type,  s^h : s¹ → s²                                   (sort s)
  f¹ : a₁¹ → … → b¹,  f² : a₁² → … → b²,
  f^h : Π x₁:a₁¹ … xₙ:aₙ¹. ded (h_b (f¹ x₁ … xₙ) = f² (h_{a₁} x₁) … (h_{aₙ} xₙ))
                                                     (operation f : a₁ → … → aₙ → b)
```

It works over LF, with a logic meta-theory `SFOL` declaring `prop`, `ded` and a
sort-polymorphic equality `eq`. Signature morphisms, i.e. maps of sort and operation
names that preserve profiles, are sent to the renaming `c^k ↦ φ(c)^k`.

Unlike the renaming functors of `Diagrams.lean`, this functor creates three
declarations from each input declaration, and the type of `f^h` is not a translation
of the type of `f`. The main work is showing that every generated declaration is
well-typed in LF.

Main results:
* `homSig_wf`: every declaration of `Hom(Σ)` is well-typed: its type is `type` or
  is derivably of type `type`.
* `homAx_typed`: in particular each homomorphism axiom `f^h` is well-typed.
* `FOMor.hom_isMorphism`: `Hom(φ)` is a well-typed morphism `Hom(Σ) → Hom(Sg')`.
* `FOMor.hom_id`, `FOMor.hom_comp`: the functor laws.
* `proj_isMorphism`, `proj_naturality`: the two projections `Σ → Hom(Σ)`, `c ↦ cᵏ`,
  are well-typed morphisms and natural in `Σ`.
-/

namespace MMT.Hom

open LF Term Judgment

/-- Derivability in LF. -/
abbrev D (S : Sig) (J : Judgment) : Prop := Derivable LF.foundation S J

theorem r0 {S j} (h : LF.Rule [] j) : D S j := .rule h (by simp)
theorem r2 {S p q j} (h : LF.Rule [p, q] j) (hp : D S p) (hq : D S q) : D S j :=
  .rule h (by simp; exact ⟨hp, hq⟩)

/-! ## The logic meta-theory -/

def sfol : ThyName := "SFOL"
def propN : GName := ⟨sfol, "prop"⟩
def dedN  : GName := ⟨sfol, "ded"⟩
def eqN   : GName := ⟨sfol, "eq"⟩
def reflN  : GName := ⟨sfol, "refl"⟩
def transN : GName := ⟨sfol, "trans"⟩
def congN  : GName := ⟨sfol, "cong"⟩

abbrev prop : Term := .const propN
def ded (p : Term) : Term := .app (.const dedN) p
def eqT (a x y : Term) : Term := .app (.app (.app (.const eqN) a) x) y

/-- `refl : Π a:type. Π x:a. ded (x = x)` -/
def reflT : Term := Pi type (Pi (.var 0) (ded (eqT (.var 1) (.var 0) (.var 0))))

/-- `trans : Π a:type. Π x y z:a. ded (x = y) → ded (y = z) → ded (x = z)` -/
def transT : Term :=
  Pi type (Pi (.var 0) (Pi (.var 1) (Pi (.var 2)
    (Pi (ded (eqT (.var 3) (.var 2) (.var 1)))
      (Pi (ded (eqT (.var 4) (.var 2) (.var 1)))
        (ded (eqT (.var 5) (.var 4) (.var 2))))))))

/-- `cong : Π a b:type. Π f g:a→b. Π x y:a. ded (f = g) → ded (x = y) → ded (f x = g y)` -/
def congT : Term :=
  Pi type (Pi type (Pi (Pi (.var 1) (.var 1)) (Pi (Pi (.var 2) (.var 2)) (Pi (.var 3) (Pi (.var 4)
    (Pi (ded (eqT (Pi (.var 5) (.var 5)) (.var 3) (.var 2)))
      (Pi (ded (eqT (.var 6) (.var 2) (.var 1)))
        (ded (eqT (.var 6) (.app (.var 5) (.var 3)) (.app (.var 4) (.var 2)))))))))))

/-- The logic: `prop : type`, `ded : prop → type`, `eq : Π a:type. a → a → prop`, and the
equality rules `refl`, `trans`, `cong`. -/
def metaSig : Sig := fun c =>
  if c = propN then some ⟨some type, none⟩
  else if c = dedN then some ⟨some (Pi prop type), none⟩
  else if c = eqN then some ⟨some (Pi type (Pi (.var 0) (Pi (.var 1) prop))), none⟩
  else if c = reflN then some ⟨some reflT, none⟩
  else if c = transN then some ⟨some transT, none⟩
  else if c = congN then some ⟨some congT, none⟩
  else none

theorem metaSig_thy {c : GName} {i : ConstInfo} (h : metaSig c = some i) : c.thy = sfol := by
  unfold metaSig at h
  repeat' split at h
  all_goals first | (subst_vars; rfl) | cases h

theorem metaSig_df {c : GName} {i : ConstInfo} (h : metaSig c = some i) : i.df = none := by
  unfold metaSig at h
  repeat' split at h
  all_goals (cases h <;> rfl)

/-- Declarations of the meta-theory only mention LF and SFOL symbols. -/
theorem metaSig_fixed {c : GName} {A : Term} {d : Option Term}
    (h : metaSig c = some ⟨some A, d⟩) {σ : Subst}
    (hσ : ∀ c', c'.thy = sfol ∨ c'.thy = LF.thy → σ c' = .const c') : A.trans σ = A := by
  have hu : A.UsesOnly (fun c' => c'.thy = sfol ∨ c'.thy = LF.thy) := by
    unfold metaSig at h
    repeat' split at h
    all_goals first
      | (cases h; simp [Term.UsesOnly, reflT, transT, congT, ded, eqT, propN, dedN, eqN,
          typeN, piN, sfol, LF.thy])
      | cases h
  rw [Term.trans_congr hu (τ := Subst.id) (fun c' h' => hσ c' h'), Term.trans_id]

/-! ## Term builders -/

/-- `a₁ → … → aₙ → b`, or `Π x₁:a₁ … xₙ:aₙ. b` when `b` mentions the variables. -/
def arrows : List Term → Term → Term
  | [], b => b
  | a :: as, b => Pi a (arrows as b)

/-- `f a₁ … aₙ`. -/
def apps : Term → List Term → Term
  | f, [] => f
  | f, a :: as => apps (.app f a) as

theorem arrows_closed {as : List Term} {b : Term} (has : ∀ a ∈ as, a.ClosedAt 0)
    (hb : b.ClosedAt 0) : (arrows as b).ClosedAt 0 := by
  induction as with
  | nil => exact hb
  | cons a as ih =>
    exact ⟨trivial, has a (by simp), (ih (fun x hx => has x (by simp [hx]))).mono (by omega)⟩

theorem arrows_trans {σ : Subst} (hP : σ piN = .const piN) (as : List Term) (b : Term) :
    (arrows as b).trans σ = arrows (as.map (·.trans σ)) (b.trans σ) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [arrows, Term.trans, hP, ih]

theorem apps_trans (σ : Subst) (f : Term) (l : List Term) :
    (apps f l).trans σ = apps (f.trans σ) (l.map (·.trans σ)) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp [apps, ih, Term.trans]

/-! ## Typing lemmas -/

/-- Typed argument lists. -/
inductive Args (S : Sig) (Γ : Ctx) : List Term → List Term → Prop where
  | nil : Args S Γ [] []
  | cons {x A xs As} : D S (.typing Γ x A) → Args S Γ xs As → Args S Γ (x :: xs) (A :: As)

theorem arrows_typed {S : Sig} {Γ : Ctx} {as : List Term} {b : Term}
    (has : ∀ a ∈ as, ∀ Γ', D S (.typing Γ' a type))
    (hb : D S (.typing (as.reverse ++ Γ) b type)) : D S (.typing Γ (arrows as b) type) := by
  induction as generalizing Γ with
  | nil => simpa [arrows] using hb
  | cons a as ih =>
    exact r2 (LF.Rule.piType Γ a (arrows as b)) (has a (by simp) Γ)
      (ih (fun x hx => has x (by simp [hx])) (by simpa using hb))

theorem apps_typed {S : Sig} {Γ : Ctx} {f b : Term} {args as : List Term}
    (hf : D S (.typing Γ f (arrows as b))) (hargs : Args S Γ args as)
    (hcl : ∀ a ∈ as, a.ClosedAt 0) (hbcl : b.ClosedAt 0) :
    D S (.typing Γ (apps f args) b) := by
  induction hargs generalizing f with
  | nil => exact hf
  | @cons x A xs As hx _ ih =>
    have h := r2 (LF.Rule.appE Γ A (arrows As b) f x) hf hx
    rw [inst_closed (arrows_closed (fun a ha => hcl a (by simp [ha])) hbcl)] at h
    exact ih h (fun a ha => hcl a (by simp [ha]))

/-! ## First-order signatures -/

/-- A first-order signature: sorts and operations with their profiles. -/
structure FOSig where
  thy : ThyName
  isSort : String → Bool
  op? : String → Option (List String × String)
  sort_not_op : ∀ n, isSort n = true → op? n = none
  op_sorts : ∀ f as b, op? f = some (as, b) → (∀ a ∈ as, isSort a = true) ∧ isSort b = true
  thy_ne_sfol : thy ≠ sfol
  thy_ne_lf : thy ≠ LF.thy

namespace FOSig

variable (Sg : FOSig)

/-- The sort `n` as a term. -/
def srt (n : String) : Term := .const ⟨Sg.thy, n⟩

/-- The LF signature of `Σ` over `SFOL`. -/
def toSig : Sig := fun d =>
  if d.thy = Sg.thy then
    match d.name with
    | .base n =>
      if Sg.isSort n then some ⟨some type, none⟩
      else (Sg.op? n).map fun p => ⟨some (arrows (p.1.map Sg.srt) (Sg.srt p.2)), none⟩
    | _ => none
  else metaSig d

variable {Sg}

theorem op_not_sort {f : String} {p} (h : Sg.op? f = some p) : Sg.isSort f = false := by
  cases hs : Sg.isSort f
  · rfl
  · rw [Sg.sort_not_op f hs] at h; cases h

end FOSig

/-! ## The theory `Hom(Σ)` -/

variable (H : ThyName)

/-- The copy `n^k` of a symbol `n` of `Σ`, for `k ∈ {1, 2, h}`. -/
def cp (k : String) (Sg : FOSig) (n : String) : GName := ⟨H, .sub k Sg.thy (.base n)⟩
def cs (k : String) (Sg : FOSig) (n : String) : Term := .const (cp H k Sg n)

/-- The variables `x₁ … xₙ` inside `n` binders. -/
def args : List String → List Term
  | [] => []
  | _ :: rest => .var rest.length :: args rest

/-- `h_{a₁} x₁ … h_{aₙ} xₙ`. -/
def hargs (Sg : FOSig) : List String → List Term
  | [] => []
  | a :: rest => .app (cs H "h" Sg a) (.var rest.length) :: hargs Sg rest

/-- The homomorphism axiom for an operation `f : as → b`. -/
def homAx (Sg : FOSig) (f : String) (as : List String) (b : String) : Term :=
  arrows (as.map (cs H "1" Sg))
    (ded (eqT (cs H "2" Sg b)
      (.app (cs H "h" Sg b) (apps (cs H "1" Sg f) (args as)))
      (apps (cs H "2" Sg f) (hargs H Sg as))))

/-- The declaration of `n^k` in `Hom(Σ)`. -/
def homInfo (Sg : FOSig) (k n : String) : Option ConstInfo :=
  if k = "1" ∨ k = "2" then
    if Sg.isSort n then some ⟨some type, none⟩
    else (Sg.op? n).map fun p => ⟨some (arrows (p.1.map (cs H k Sg)) (cs H k Sg p.2)), none⟩
  else if k = "h" then
    if Sg.isSort n then some ⟨some (Pi (cs H "1" Sg n) (cs H "2" Sg n)), none⟩
    else (Sg.op? n).map fun p => ⟨some (homAx H Sg n p.1 p.2), none⟩
  else none

/-- The theory `Hom(Σ)`, named `H`, over `SFOL`. -/
def homSig (Sg : FOSig) : Sig := fun d =>
  if d.thy = H then
    match d.name with
    | .sub k thy (.base n) => if thy = Sg.thy then homInfo H Sg k n else none
    | _ => none
  else metaSig d

variable {H}

theorem homSig_cp {Sg : FOSig} {k n : String} : homSig H Sg (cp H k Sg n) = homInfo H Sg k n := by
  simp [homSig, cp]

theorem homSig_meta {Sg : FOSig} {c : GName} (h : c.thy ≠ H) : homSig H Sg c = metaSig c := by
  simp [homSig, h]

theorem homSig_cases {Sg : FOSig} {c : GName} {i : ConstInfo} (h : homSig H Sg c = some i) :
    (∃ k n, c = cp H k Sg n ∧ homInfo H Sg k n = some i) ∨ (c.thy ≠ H ∧ metaSig c = some i) := by
  obtain ⟨t, nm⟩ := c
  unfold homSig at h
  by_cases ht : t = H
  · subst ht
    simp only [↓reduceIte] at h
    split at h
    · rename_i k thy n
      split at h
      · subst_vars; exact .inl ⟨k, n, rfl, h⟩
      · cases h
    · cases h
  · simp only [ht, ↓reduceIte] at h
    exact .inr ⟨ht, h⟩

theorem homInfo_df {Sg : FOSig} {k n : String} {i : ConstInfo} (h : homInfo H Sg k n = some i) :
    i.df = none := by
  unfold homInfo at h
  repeat' split at h
  all_goals first
    | (cases h <;> rfl)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)

theorem homSig_df {Sg : FOSig} {c : GName} {i : ConstInfo} (h : homSig H Sg c = some i) :
    i.df = none := by
  rcases homSig_cases h with ⟨_, _, _, h⟩ | ⟨_, h⟩
  · exact homInfo_df h
  · exact metaSig_df h

/-! ## Well-typedness of `Hom(Σ)` -/

section WF

variable {Sg : FOSig} (hH : H ≠ sfol)
include hH

theorem meta_typed {c : GName} {A : Term} {d : Option Term} (h : metaSig c = some ⟨some A, d⟩)
    (Γ : Ctx) : D (homSig H Sg) (.typing Γ (.const c) A) :=
  .const (by rw [homSig_meta (by rw [metaSig_thy h]; exact Ne.symm hH)]; exact h)

omit hH in
theorem sort_typed {k n : String} (hk : k = "1" ∨ k = "2") (hs : Sg.isSort n = true)
    (Γ : Ctx) : D (homSig H Sg) (.typing Γ (cs H k Sg n) type) :=
  .const (c := cp H k Sg n) (d := none) (by rw [homSig_cp]; simp [homInfo, hk, hs])

omit hH in
theorem op_typed {k f : String} {as : List String} {b : String} (hk : k = "1" ∨ k = "2")
    (hf : Sg.op? f = some (as, b)) (Γ : Ctx) :
    D (homSig H Sg) (.typing Γ (cs H k Sg f) (arrows (as.map (cs H k Sg)) (cs H k Sg b))) :=
  .const (c := cp H k Sg f) (d := none)
    (by rw [homSig_cp]; simp [homInfo, hk, FOSig.op_not_sort hf, hf, cs])

omit hH in
theorem hom_typed {n : String} (hs : Sg.isSort n = true) (Γ : Ctx) :
    D (homSig H Sg) (.typing Γ (cs H "h" Sg n) (Pi (cs H "1" Sg n) (cs H "2" Sg n))) :=
  .const (c := cp H "h" Sg n) (d := none) (by rw [homSig_cp]; simp [homInfo, hs, cs])

omit hH in
theorem args_typed (T : String → Term) (hT : ∀ a, ∃ c, T a = .const c) :
    ∀ (as : List String) (Γ₀ : Ctx),
      Args (homSig H Sg) ((as.map T).reverse ++ Γ₀) (args as) (as.map T)
  | [], _ => .nil
  | a :: rest, Γ₀ => by
    obtain ⟨c, hc⟩ := hT a
    have hv : ((rest.map T).reverse ++ (T a :: Γ₀))[rest.length]? = some (T a) := by
      rw [List.getElem?_append_right (by simp)]; simp
    have hx := r0 (S := homSig H Sg) (LF.Rule.var _ rest.length (T a) hv)
    have hl : liftN (rest.length + 1) 0 (T a) = T a := by rw [hc]; rfl
    rw [hl] at hx
    have e : ((a :: rest).map T).reverse ++ Γ₀ = (rest.map T).reverse ++ (T a :: Γ₀) := by simp
    rw [e]
    exact .cons hx (args_typed T hT rest (T a :: Γ₀))

omit hH in
theorem hargs_typed (as : List String) (has : ∀ a ∈ as, Sg.isSort a = true) (Γ₀ : Ctx) :
    Args (homSig H Sg) ((as.map (cs H "1" Sg)).reverse ++ Γ₀) (hargs H Sg as)
      (as.map (cs H "2" Sg)) := by
  induction as generalizing Γ₀ with
  | nil => exact .nil
  | cons a rest ih =>
    have hv : ((rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀))[rest.length]? =
        some (cs H "1" Sg a) := by
      rw [List.getElem?_append_right (by simp)]; simp
    have hx : D (homSig H Sg) (.typing _ (.var rest.length) (cs H "1" Sg a)) :=
      r0 (LF.Rule.var _ rest.length _ hv)
    have happ : D (homSig H Sg) (.typing _ (.app (cs H "h" Sg a) (.var rest.length))
        (cs H "2" Sg a)) :=
      r2 (LF.Rule.appE _ _ _ _ _) (hom_typed (has a (by simp)) _) hx
    have e : ((a :: rest).map (cs H "1" Sg)).reverse ++ Γ₀ =
        (rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀) := by simp
    rw [e]
    exact .cons happ (ih (fun x hx => has x (by simp [hx])) (cs H "1" Sg a :: Γ₀))

/-- **Each homomorphism axiom is well-typed.** -/
theorem homAx_typed {f : String} {as : List String} {b : String}
    (hf : Sg.op? f = some (as, b)) : D (homSig H Sg) (.typing [] (homAx H Sg f as b) type) := by
  obtain ⟨has, hb⟩ := Sg.op_sorts f as b hf
  have hcl : ∀ k, ∀ a ∈ as.map (cs H k Sg), a.ClosedAt 0 := by
    intro k a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial
  apply arrows_typed
  · intro a ha Γ'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact sort_typed (.inl rfl) (has x hx) Γ'
  · -- inside the binders
    simp only [List.append_nil]
    have hX : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse
        (.app (cs H "h" Sg b) (apps (cs H "1" Sg f) (args as))) (cs H "2" Sg b)) := by
      have h1 := apps_typed (op_typed (.inl rfl) hf _)
        (by simpa using args_typed (cs H "1" Sg) (fun a => ⟨_, rfl⟩) as [])
        (hcl "1") trivial
      exact r2 (LF.Rule.appE _ _ _ _ _) (hom_typed hb _) h1
    have hY : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse
        (apps (cs H "2" Sg f) (hargs H Sg as)) (cs H "2" Sg b)) :=
      apps_typed (op_typed (.inr rfl) hf _)
        (by simpa using hargs_typed as has []) (hcl "2") trivial
    have heq : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse (.const eqN)
        (Pi type (Pi (.var 0) (Pi (.var 1) prop)))) :=
      meta_typed hH (d := none) (by simp [metaSig, eqN, propN, dedN]) _
    have hded : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse (.const dedN)
        (Pi prop type)) :=
      meta_typed hH (d := none) (by simp [metaSig, propN, dedN]) _
    have e1 : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse
        (.app (.const eqN) (cs H "2" Sg b)) (Pi (cs H "2" Sg b) (Pi (cs H "2" Sg b) prop))) :=
      r2 (LF.Rule.appE _ type (Pi (.var 0) (Pi (.var 1) prop)) _ _) heq
        (sort_typed (.inr rfl) hb _)
    have e2 : D (homSig H Sg) (.typing (as.map (cs H "1" Sg)).reverse
        (.app (.app (.const eqN) (cs H "2" Sg b))
          (.app (cs H "h" Sg b) (apps (cs H "1" Sg f) (args as))))
        (Pi (cs H "2" Sg b) prop)) :=
      r2 (LF.Rule.appE _ (cs H "2" Sg b) (Pi (cs H "2" Sg b) prop) _ _) e1 hX
    have e3 := r2 (LF.Rule.appE _ (cs H "2" Sg b) prop _ _) e2 hY
    exact r2 (LF.Rule.appE _ prop type (.const dedN) _) hded e3

/-- **`Hom(Σ)` is well-formed**: every declaration of a copy or homomorphism symbol has
a well-typed type (either `type` itself, or a type of kind `type`). -/
theorem homSig_wf {k n : String} {A : Term} {d : Option Term}
    (h : homSig H Sg (cp H k Sg n) = some ⟨some A, d⟩) :
    A = type ∨ D (homSig H Sg) (.typing [] A type) := by
  rw [homSig_cp] at h
  unfold homInfo at h
  by_cases hk : k = "1" ∨ k = "2"
  · simp only [hk, ↓reduceIte] at h
    by_cases hs : Sg.isSort n = true
    · simp only [hs, ↓reduceIte] at h; cases h; exact .inl rfl
    · simp only [hs] at h
      obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp h
      cases hi
      obtain ⟨has, hb⟩ := Sg.op_sorts n as b hf
      refine .inr (arrows_typed ?_ ?_)
      · intro a ha Γ'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact sort_typed hk (has x hx) Γ'
      · exact sort_typed hk hb _
  · simp only [hk, ↓reduceIte] at h
    by_cases hh : k = "h"
    · subst hh
      simp only [↓reduceIte] at h
      by_cases hs : Sg.isSort n = true
      · simp only [hs, ↓reduceIte] at h; cases h
        exact .inr (r2 (LF.Rule.piType _ _ _) (sort_typed (.inl rfl) hs _)
          (sort_typed (.inr rfl) hs _))
      · simp only [hs] at h
        obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp h
        cases hi
        exact .inr (homAx_typed hH hf)
    · simp [hh] at h

end WF

/-! ## Signature morphisms and `Hom(φ)` -/

/-- A morphism of first-order signatures: a map of names preserving sorts and profiles. -/
structure FOMor (Sg Sg' : FOSig) where
  φ : String → String
  sort : ∀ n, Sg.isSort n = true → Sg'.isSort (φ n) = true
  op : ∀ f p, Sg.op? f = some p → Sg'.op? (φ f) = some (p.1.map φ, φ p.2)

namespace FOMor

variable {Sg Sg' Sg'' : FOSig}

def id (Sg : FOSig) : FOMor Sg Sg where
  φ n := n
  sort _ h := h
  op f p h := by simp [h]

def comp (μ : FOMor Sg Sg') (ν : FOMor Sg' Sg'') : FOMor Sg Sg'' where
  φ n := ν.φ (μ.φ n)
  sort n h := ν.sort _ (μ.sort n h)
  op f p h := by rw [ν.op _ _ (μ.op f p h)]; simp [Function.comp_def]

variable (μ : FOMor Sg Sg') (H H' : ThyName)

/-- `Hom(φ)`: the renaming `nᵏ ↦ φ(n)ᵏ`, identity on the meta-theory. -/
def hom : Subst := fun d =>
  if d.thy = H then
    match d.name with
    | .sub k thy (.base n) => if thy = Sg.thy then cs H' k Sg' (μ.φ n) else .const d
    | _ => .const d
  else .const d

variable {μ H H'}

theorem hom_cp {k n : String} : μ.hom H H' (cp H k Sg n) = cs H' k Sg' (μ.φ n) := by
  simp [hom, cp]

theorem hom_other {d : GName} (h : d.thy ≠ H) : μ.hom H H' d = .const d := by
  simp [hom, h]

theorem hom_cs {k n : String} : (cs H k Sg n).trans (μ.hom H H') = cs H' k Sg' (μ.φ n) := by
  simp [cs, Term.trans, hom_cp]

section
variable (hH : H ≠ sfol) (hL : H ≠ LF.thy)
include hH hL

theorem hom_fix {c : GName} (h : c.thy = sfol ∨ c.thy = LF.thy) : μ.hom H H' c = .const c := by
  apply hom_other; rcases h with h | h <;> rw [h]
  · exact Ne.symm hH
  · exact Ne.symm hL

theorem hom_homAx (f : String) (as : List String) (b : String) :
    (homAx H Sg f as b).trans (μ.hom H H') = homAx H' Sg' (μ.φ f) (as.map μ.φ) (μ.φ b) := by
  have hP : μ.hom H H' piN = .const piN := hom_fix hH hL (.inr rfl)
  have hD : μ.hom H H' dedN = .const dedN := hom_fix hH hL (.inl rfl)
  have hE : μ.hom H H' eqN = .const eqN := hom_fix hH hL (.inl rfl)
  have hargs_eq : ∀ l : List String, args (l.map μ.φ) = args l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [args, ih]
  have hargs_tr : ∀ l : List String, (args l).map (·.trans (μ.hom H H')) = args l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [args, ih, Term.trans]
  have hh_tr : ∀ l : List String,
      (hargs H Sg l).map (·.trans (μ.hom H H')) = hargs H' Sg' (l.map μ.φ) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [hargs, ih, Term.trans, hom_cs]
  simp [homAx, arrows_trans hP, apps_trans, ded, eqT, Term.trans, hD, hE, hom_cs, hargs_tr,
    hh_tr, hargs_eq, Function.comp_def]

/-- **`Hom(φ)` is a well-typed morphism** `Hom(Σ) → Hom(Sg')`. -/
theorem hom_isMorphism (hH' : H' ≠ sfol) :
    IsMorphism LF.foundation (homSig H Sg) (homSig H' Sg') (μ.hom H H') where
  closed d := by unfold hom; repeat (first | split | trivial)
  fixMeta c hc := hom_fix hH hL (.inr hc)
  typed {c A d} hc := by
    rcases homSig_cases hc with ⟨k, n, rfl, hi⟩ | ⟨hne, hm⟩
    · rw [hom_cp]
      have hdf := homInfo_df hi; simp only at hdf; subst hdf
      unfold homInfo at hi
      refine .const (d := none) ?_
      rw [homSig_cp]
      unfold homInfo
      by_cases hk : k = "1" ∨ k = "2"
      · simp only [hk, ↓reduceIte] at hi ⊢
        by_cases hs : Sg.isSort n = true
        · simp only [hs, ↓reduceIte] at hi; cases hi
          simp [μ.sort n hs, Term.trans, hom_fix hH hL (c := typeN) (.inr rfl)]
        · simp only [hs] at hi
          obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp hi
          cases hi
          have hf' := μ.op n _ hf
          simp [FOSig.op_not_sort hf', hf', arrows_trans (hom_fix hH hL (.inr rfl)), hom_cs,
            Function.comp_def]
      · simp only [hk, ↓reduceIte] at hi ⊢
        by_cases hh : k = "h"
        · subst hh
          simp only [↓reduceIte] at hi ⊢
          by_cases hs : Sg.isSort n = true
          · simp only [hs, ↓reduceIte] at hi; cases hi
            simp [μ.sort n hs, Term.trans, hom_fix hH hL (c := piN) (.inr rfl), hom_cs]
          · simp only [hs] at hi
            obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp hi
            cases hi
            have hf' := μ.op n _ hf
            simp [FOSig.op_not_sort hf', hf', hom_homAx hH hL]
        · simp [hh] at hi
    · rw [hom_other hne, metaSig_fixed hm (fun c' h => hom_fix hH hL h)]
      refine .const (d := d) ?_
      rw [homSig_meta (by rw [metaSig_thy hm]; exact Ne.symm hH')]
      exact hm
  defn {c A d} hc := by cases homSig_df hc

end

/-- Functor law: identities. -/
theorem hom_id : (FOMor.id Sg).hom H H = Subst.id := by
  funext d
  obtain ⟨t, nm⟩ := d
  unfold hom
  by_cases ht : t = H
  · subst ht
    simp only [↓reduceIte]
    split
    · split
      · subst_vars; rfl
      · rfl
    · rfl
  · simp [ht]; rfl

/-- Functor law: composition, on the constants of `Hom(Σ)`. -/
theorem hom_comp (μ : FOMor Sg Sg') (ν : FOMor Sg' Sg'') {H H' H'' : ThyName} (hH' : H' ≠ sfol)
    {d : GName} (hd : (homSig H Sg d).isSome = true) :
    (μ.comp ν).hom H H'' d = ((μ.hom H H').comp (ν.hom H' H'')) d := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hd
  rcases homSig_cases hi with ⟨k, n, rfl, -⟩ | ⟨hne, hm⟩
  · simp only [hom_cp, Subst.comp, cs, Term.trans]; rfl
  · have : d.thy ≠ H' := by rw [metaSig_thy hm]; exact Ne.symm hH'
    simp [hom_other hne, Subst.comp, Term.trans, hom_other this]

end FOMor

/-! ## The projections `Σ → Hom(Σ)` -/

/-- The projection `c ↦ cᵏ` for `k ∈ {1, 2}`. -/
def proj (H : ThyName) (k : String) (Sg : FOSig) : Subst := fun d =>
  if d.thy = Sg.thy then
    match d.name with
    | .base n => cs H k Sg n
    | _ => .const d
  else .const d

/-- The underlying renaming of a signature morphism, on `Σ` itself. -/
def FOMor.base {Sg Sg' : FOSig} (μ : FOMor Sg Sg') : Subst := fun d =>
  if d.thy = Sg.thy then
    match d.name with
    | .base n => Sg'.srt (μ.φ n)
    | _ => .const d
  else .const d

theorem proj_srt {k : String} {Sg : FOSig} {n : String} :
    (Sg.srt n).trans (proj H k Sg) = cs H k Sg n := by
  simp [FOSig.srt, Term.trans, proj]

theorem proj_other {k : String} {Sg : FOSig} {d : GName} (h : d.thy ≠ Sg.thy) :
    proj H k Sg d = .const d := by simp [proj, h]

theorem toSig_cases {Sg : FOSig} {c : GName} {i : ConstInfo} (h : Sg.toSig c = some i) :
    (∃ n, c = ⟨Sg.thy, .base n⟩ ∧
      ((Sg.isSort n = true ∧ i = ⟨some type, none⟩) ∨
       (∃ as b, Sg.op? n = some (as, b) ∧
         i = ⟨some (arrows (as.map Sg.srt) (Sg.srt b)), none⟩))) ∨
    (c.thy ≠ Sg.thy ∧ metaSig c = some i) := by
  obtain ⟨t, nm⟩ := c
  unfold FOSig.toSig at h
  by_cases ht : t = Sg.thy
  · subst ht
    simp only [↓reduceIte] at h
    split at h
    · rename_i n
      refine .inl ⟨n, rfl, ?_⟩
      by_cases hs : Sg.isSort n = true
      · simp only [hs, ↓reduceIte] at h; cases h; exact .inl ⟨hs, rfl⟩
      · simp only [hs] at h
        obtain ⟨⟨as, b⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .inr ⟨as, b, hf, rfl⟩
    · cases h
  · simp only [ht, ↓reduceIte] at h
    exact .inr ⟨ht, h⟩

/-- **The projections are well-typed morphisms** `Σ → Hom(Σ)`. -/
theorem proj_isMorphism {k : String} (hk : k = "1" ∨ k = "2") {Sg : FOSig} (hH : H ≠ sfol) :
    IsMorphism LF.foundation Sg.toSig (homSig H Sg) (proj H k Sg) where
  closed d := by unfold proj; repeat (first | split | trivial)
  fixMeta c hc := proj_other (by
    simp only [LF.foundation] at hc; rw [hc]; exact Ne.symm Sg.thy_ne_lf)
  typed {c A d} hc := by
    rcases toSig_cases hc with ⟨n, rfl, ⟨hs, hi⟩ | ⟨as, b, hf, hi⟩⟩ | ⟨hne, hm⟩
    · cases hi
      have hp : proj H k Sg ⟨Sg.thy, .base n⟩ = cs H k Sg n := by simp [proj]
      have ht : type.trans (proj H k Sg) = type :=
        proj_other (show LF.thy ≠ Sg.thy from Ne.symm Sg.thy_ne_lf)
      rw [hp, ht]
      exact .const (c := cp H k Sg n) (d := none) (by rw [homSig_cp]; simp [homInfo, hk, hs])
    · cases hi
      have hp : proj H k Sg ⟨Sg.thy, .base n⟩ = cs H k Sg n := by simp [proj]
      have hP : proj H k Sg piN = .const piN :=
        proj_other (show LF.thy ≠ Sg.thy from Ne.symm Sg.thy_ne_lf)
      rw [hp, arrows_trans hP]
      refine .const (c := cp H k Sg n) (d := none) ?_
      rw [homSig_cp]
      simp [homInfo, hk, FOSig.op_not_sort hf, hf, proj_srt, Function.comp_def]
    · rw [proj_other hne, metaSig_fixed hm (fun c' h => proj_other (by
        rcases h with h | h <;> rw [h]
        · exact Ne.symm Sg.thy_ne_sfol
        · exact Ne.symm Sg.thy_ne_lf))]
      refine .const (d := d) ?_
      rw [homSig_meta (by rw [metaSig_thy hm]; exact Ne.symm hH)]
      exact hm
  defn {c A d} hc := by
    rcases toSig_cases hc with ⟨n, rfl, ⟨_, hi⟩ | ⟨_, _, _, hi⟩⟩ | ⟨_, hm⟩
    · cases hi
    · cases hi
    · cases metaSig_df hm

/-- **Naturality** of the projections: `proj_Σ ; Hom(φ) = φ ; proj_Sg'` on the constants
of `Σ`. -/
theorem proj_naturality {k : String} {Sg Sg' : FOSig} (μ : FOMor Sg Sg') {H H' : ThyName}
    (hH : H ≠ sfol) (hL : H ≠ LF.thy) {c : GName} (hc : (Sg.toSig c).isSome = true) :
    ((proj H k Sg).comp (μ.hom H H')) c = (μ.base.comp (proj H' k Sg')) c := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hc
  rcases toSig_cases hi with ⟨n, rfl, -⟩ | ⟨hne, hm⟩
  · simp [Subst.comp, proj, FOMor.base, FOMor.hom_cs, proj_srt]
  · have h1 : c.thy = sfol := metaSig_thy hm
    have h2 : c.thy ≠ Sg'.thy := by rw [h1]; exact Ne.symm Sg'.thy_ne_sfol
    simp [Subst.comp, proj_other hne, Term.trans, FOMor.hom_fix hH hL (.inl h1), FOMor.base,
      hne, proj_other h2]

end MMT.Hom
