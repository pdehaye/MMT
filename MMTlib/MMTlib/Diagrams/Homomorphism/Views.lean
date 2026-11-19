import MMTlib.Diagrams.Homomorphism.Basic

/-!
# The homomorphism functor on views with compound terms

`Homomorphism.lean` applies the homomorphism functor to signature morphisms, which
send symbols to symbols. Here a view may send an operation `f : a₁ → … → aₙ → b` to an
arbitrary first-order term `t` over the codomain signature, with free variables
`x₁ … xₙ`. MMT represents the assignment as `f ↦ λx⃗. t`.

`Hom(φ)` must then send the axiom `f^h` to a *proof*
`λx⃗. P(t) : Π x⃗. ded (h (f¹ x⃗) = f² (h x⃗))[φ]`, where `P(t)` is built by induction
on `t` from the axioms `g^h` of the codomain and the logic's `refl`, `trans` and
`cong`. The translated type contains β-redexes `(λx⃗. t¹) x⃗`, so `P(t)` is moved to it
by LF's conversion rule.

Our LF has no substitution lemma for derivations. To avoid needing one, every
intermediate term is kept as the encoding of a first-order term under a variable
valuation, and its typing is proved directly.

This file contains the infrastructure:
* `liftN_zero`, `inst_liftN`: de Bruijn identities for instantiating telescopes with
  open terms;
* `substTele`: instantiation of a whole telescope, and `apps_typed_dep`: typing of
  applications to it;
* `refl_typed`, `trans_typed`, `cong_typed`: typing of the logic's equality rules.
-/

namespace MMT.Hom

open LF Term Judgment

/-! ## de Bruijn identities -/

theorem liftN_zero (c : Nat) (t : Term) : liftN 0 c t = t := by
  induction t generalizing c with
  | var i => by_cases h : i < c <;> simp [liftN, h]
  | const _ => rfl
  | app f a ihf iha => simp [liftN, ihf, iha]
  | bind b A t ihb ihA iht => simp [liftN, ihb, ihA, iht]

/-- Substituting into a variable that a lift skipped over. -/
theorem inst_liftN {k c j : Nat} (v t : Term) (h1 : c ≤ j) (h2 : j ≤ c + k) :
    inst j v (liftN (k + 1) c t) = liftN k c t := by
  induction t generalizing c j with
  | var i =>
    by_cases hi : i < c
    · have : i < j := by omega
      simp [liftN, inst, hi, this]
    · have h3 : ¬ (i + (k + 1) < j) := by omega
      have h4 : ¬ (i + (k + 1) = j) := by omega
      simp only [liftN, hi, ↓reduceIte, inst, h3, h4]
      show Term.var (i + (k + 1) - 1) = Term.var (i + k)
      congr 1
  | const _ => rfl
  | app f a ihf iha => simp [liftN, inst, ihf h1 h2, iha h1 h2]
  | bind b A t ihb ihA iht =>
    simp [liftN, inst, ihb h1 h2, ihA h1 h2, iht (by omega : c + 1 ≤ j + 1) (by omega)]

/-- Specialization used for telescopes: lifted by `j + 1`, substituted at `j`. -/
theorem inst_liftN_succ (j : Nat) (v t : Term) : inst j v (liftN (j + 1) 0 t) = liftN j 0 t :=
  inst_liftN v t (Nat.zero_le _) (by omega)

/-! ## Instantiating telescopes -/

/-- `substTele [u₁, …, uₙ] B` instantiates the `n` binders of a telescope body `B`,
outermost first. -/
def substTele : List Term → Term → Term
  | [], B => B
  | u :: us, B => substTele us (inst us.length u B)

theorem substTele_const (us : List Term) (c : GName) : substTele us (.const c) = .const c := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [substTele, inst, ih]

theorem substTele_app (us : List Term) (f a : Term) :
    substTele us (.app f a) = .app (substTele us f) (substTele us a) := by
  induction us generalizing f a with
  | nil => rfl
  | cons u us ih => simp [substTele, inst, ih]

theorem substTele_closed {us : List Term} {t : Term} (h : t.ClosedAt 0) : substTele us t = t := by
  induction us generalizing t with
  | nil => rfl
  | cons u us ih => simp [substTele, inst_closed h, ih h]

theorem substTele_apps (us : List Term) (F : Term) (xs : List Term) :
    substTele us (apps F xs) = apps (substTele us F) (xs.map (substTele us)) := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp [apps, ih, substTele_app]

/-- The variables `var (n-1), …, var 0`. -/
def varsDesc : Nat → List Term
  | 0 => []
  | n + 1 => .var n :: varsDesc n

theorem varsDesc_length (n : Nat) : (varsDesc n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [varsDesc, ih]

theorem varsDesc_inst (r : Nat) (u : Term) : (varsDesc r).map (inst r u) = varsDesc r := by
  suffices ∀ m, m ≤ r → (varsDesc m).map (inst r u) = varsDesc m from this r (Nat.le_refl _)
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    have : m < r := by omega
    simp [varsDesc, inst, this, ih (by omega)]

theorem map_substTele_cons (u : Term) (rest l : List Term) :
    l.map (substTele (u :: rest)) = (l.map (inst rest.length u)).map (substTele rest) := by
  simp [substTele, List.map_map, Function.comp_def]

/-- Instantiating a telescope at its own variables, with earlier arguments `done`
already substituted. -/
theorem substTele_varsDesc_aux :
    ∀ (rest done : List Term),
      (done.map (liftN rest.length 0) ++ varsDesc rest.length).map (substTele rest) = done ++ rest
  | [], done => by simp [varsDesc, substTele, liftN_zero, Function.comp_def]
  | u :: rest, done => by
    have h := substTele_varsDesc_aux rest (done ++ [u])
    have e1 : (done.map (liftN (rest.length + 1) 0) ++ varsDesc (rest.length + 1)).map
        (inst rest.length u) = (done ++ [u]).map (liftN rest.length 0) ++ varsDesc rest.length := by
      rw [List.map_append, List.map_map, varsDesc, List.map_cons, varsDesc_inst]
      have : (inst rest.length u ∘ liftN (rest.length + 1) 0) = liftN rest.length 0 := by
        funext x; exact inst_liftN_succ _ _ _
      rw [this]
      simp [inst]
    rw [List.length_cons, map_substTele_cons, e1, h]
    simp

theorem substTele_varsDesc (us : List Term) : (varsDesc us.length).map (substTele us) = us := by
  simpa using substTele_varsDesc_aux us []

theorem Args.length_eq {S : Sig} {Γ : Ctx} {xs As : List Term} (h : Args S Γ xs As) :
    xs.length = As.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem inst_arrows {As : List Term} (hAs : ∀ a ∈ As, a.ClosedAt 0) (j : Nat) (x B : Term) :
    inst j x (arrows As B) = arrows As (inst (j + As.length) x B) := by
  induction As generalizing j with
  | nil => rfl
  | cons a As ih =>
    simp only [arrows, inst, List.length_cons]
    rw [inst_closed (hAs a (by simp)), ih (fun x hx => hAs x (by simp [hx]))]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- Applications to a dependent telescope: the result type is the instantiated body. -/
theorem apps_typed_dep {S : Sig} {Γ : Ctx} {f B : Term} {us As : List Term}
    (hf : D S (.typing Γ f (arrows As B))) (hAs : ∀ a ∈ As, a.ClosedAt 0)
    (hus : Args S Γ us As) : D S (.typing Γ (apps f us) (substTele us B)) := by
  induction hus generalizing f B with
  | nil => exact hf
  | @cons x A xs As' hx hxs ih =>
    have h := r2 (LF.Rule.appE Γ A (arrows As' B) f x) hf hx
    rw [inst_arrows (fun a ha => hAs a (by simp [ha]))] at h
    have := ih h (fun a ha => hAs a (by simp [ha]))
    simpa [apps, substTele, hxs.length_eq] using this

/-- Application with an explicitly computed result type. -/
theorem appE' {S : Sig} {Γ : Ctx} {f a A B C : Term}
    (hf : D S (.typing Γ f (Pi A B))) (ha : D S (.typing Γ a A)) (h : inst 0 a B = C) :
    D S (.typing Γ (.app f a) C) := h ▸ r2 (LF.Rule.appE Γ A B f a) hf ha

/-! ## The equality rules of the logic -/

/-- `refl A x : ded (x = x)` -/
def reflP (A x : Term) : Term := .app (.app (.const reflN) A) x

/-- `trans A x y z p q : ded (x = z)` -/
def transP (A x y z p q : Term) : Term :=
  apps (.const transN) [A, x, y, z, p, q]

/-- `cong A B f g x y p q : ded (f x = g y)` -/
def congP (A B f g x y p q : Term) : Term :=
  apps (.const congN) [A, B, f, g, x, y, p, q]

section Rules

variable {S : Sig} (hS : ∀ c, c.thy = sfol → S c = metaSig c) {Γ : Ctx}
include hS

theorem meta_const {c : GName} {A : Term} (h : metaSig c = some ⟨some A, none⟩) (Γ : Ctx) :
    D S (.typing Γ (.const c) A) :=
  .const (by rw [hS c (metaSig_thy h)]; exact h)

theorem refl_typed {A x : Term} (hAt : D S (.typing Γ A type)) (hAc : A.ClosedAt 0)
    (hx : D S (.typing Γ x A)) : D S (.typing Γ (reflP A x) (ded (eqT A x x))) := by
  have h0 : D S (.typing Γ (.const reflN) reflT) :=
    meta_const hS (by simp [metaSig, reflN, propN, dedN, eqN]) Γ
  have h1 := appE' (C := Pi A (ded (eqT A (.var 0) (.var 0)))) h0 hAt
    (by simp [inst, ded, eqT, liftN_closed hAc])
  exact appE' h1 hx (by simp [inst, ded, eqT, liftN_zero, inst_closed hAc])

theorem trans_typed {A x y z p q : Term} (hAt : D S (.typing Γ A type)) (hAc : A.ClosedAt 0)
    (hx : D S (.typing Γ x A)) (hy : D S (.typing Γ y A)) (hz : D S (.typing Γ z A))
    (hp : D S (.typing Γ p (ded (eqT A x y)))) (hq : D S (.typing Γ q (ded (eqT A y z)))) :
    D S (.typing Γ (transP A x y z p q) (ded (eqT A x z))) := by
  have h0 : D S (.typing Γ (.const transN) transT) :=
    meta_const hS (by simp [metaSig, transN, reflN, propN, dedN, eqN]) Γ
  have h1 := appE' (C := Pi A (Pi A (Pi A (Pi (ded (eqT A (.var 2) (.var 1)))
      (Pi (ded (eqT A (.var 2) (.var 1))) (ded (eqT A (.var 4) (.var 2)))))))) h0 hAt
    (by simp [inst, ded, eqT, liftN_closed hAc])
  have h2 := appE' (C := Pi A (Pi A (Pi (ded (eqT A (liftN 2 0 x) (.var 1)))
      (Pi (ded (eqT A (.var 2) (.var 1))) (ded (eqT A (liftN 4 0 x) (.var 2))))))) h1 hx
    (by simp [inst, ded, eqT, inst_closed hAc])
  have h3 := appE' (C := Pi A (Pi (ded (eqT A (liftN 1 0 x) (liftN 1 0 y)))
      (Pi (ded (eqT A (liftN 2 0 y) (.var 1))) (ded (eqT A (liftN 3 0 x) (.var 2)))))) h2 hy
    (by simp [inst, ded, eqT, inst_closed hAc, inst_liftN_succ])
  have h4 := appE' (C := Pi (ded (eqT A x y))
      (Pi (ded (eqT A (liftN 1 0 y) (liftN 1 0 z))) (ded (eqT A (liftN 2 0 x) (liftN 2 0 z)))))
    h3 hz (by simp [inst, ded, eqT, inst_closed hAc, inst_liftN_succ, liftN_zero])
  have h5 := appE' (C := Pi (ded (eqT A y z)) (ded (eqT A (liftN 1 0 x) (liftN 1 0 z)))) h4 hp
    (by simp [inst, ded, eqT, inst_closed hAc, inst_liftN_succ, liftN_zero])
  exact appE' h5 hq (by simp [inst, ded, eqT, inst_closed hAc, inst_liftN_succ, liftN_zero])

theorem cong_typed {A B f g x y p q : Term} (hAt : D S (.typing Γ A type))
    (hBt : D S (.typing Γ B type)) (hAc : A.ClosedAt 0) (hBc : B.ClosedAt 0)
    (hf : D S (.typing Γ f (Pi A B))) (hg : D S (.typing Γ g (Pi A B)))
    (hx : D S (.typing Γ x A)) (hy : D S (.typing Γ y A))
    (hp : D S (.typing Γ p (ded (eqT (Pi A B) f g))))
    (hq : D S (.typing Γ q (ded (eqT A x y)))) :
    D S (.typing Γ (congP A B f g x y p q) (ded (eqT B (.app f x) (.app g y)))) := by
  have h0 : D S (.typing Γ (.const congN) congT) :=
    meta_const hS (by simp [metaSig, congN, transN, reflN, propN, dedN, eqN]) Γ
  have h1 := appE' (C := Pi type (Pi (Pi A (.var 1)) (Pi (Pi A (.var 2)) (Pi A (Pi A
      (Pi (ded (eqT (Pi A (.var 5)) (.var 3) (.var 2)))
        (Pi (ded (eqT A (.var 2) (.var 1)))
          (ded (eqT (.var 6) (.app (.var 5) (.var 3)) (.app (.var 4) (.var 2))))))))))) h0 hAt
    (by simp [inst, ded, eqT, liftN_closed hAc])
  have h2 := appE' (C := Pi (Pi A B) (Pi (Pi A B) (Pi A (Pi A
      (Pi (ded (eqT (Pi A B) (.var 3) (.var 2)))
        (Pi (ded (eqT A (.var 2) (.var 1)))
          (ded (eqT B (.app (.var 5) (.var 3)) (.app (.var 4) (.var 2)))))))))) h1 hBt
    (by simp [inst, ded, eqT, liftN_closed hBc, inst_closed hAc])
  have h3 := appE' (C := Pi (Pi A B) (Pi A (Pi A
      (Pi (ded (eqT (Pi A B) (liftN 3 0 f) (.var 2)))
        (Pi (ded (eqT A (.var 2) (.var 1)))
          (ded (eqT B (.app (liftN 5 0 f) (.var 3)) (.app (.var 4) (.var 2))))))))) h2 hf
    (by simp [inst, ded, eqT, inst_closed hAc, inst_closed hBc])
  have h4 := appE' (C := Pi A (Pi A
      (Pi (ded (eqT (Pi A B) (liftN 2 0 f) (liftN 2 0 g)))
        (Pi (ded (eqT A (.var 2) (.var 1)))
          (ded (eqT B (.app (liftN 4 0 f) (.var 3)) (.app (liftN 4 0 g) (.var 2)))))))) h3 hg
    (by simp [inst, ded, eqT, inst_closed hAc, inst_closed hBc, inst_liftN_succ])
  have h5 := appE' (C := Pi A
      (Pi (ded (eqT (Pi A B) (liftN 1 0 f) (liftN 1 0 g)))
        (Pi (ded (eqT A (liftN 2 0 x) (.var 1)))
          (ded (eqT B (.app (liftN 3 0 f) (liftN 3 0 x)) (.app (liftN 3 0 g) (.var 2))))))) h4 hx
    (by simp [inst, ded, eqT, inst_closed hAc, inst_closed hBc, inst_liftN_succ])
  have h6 := appE' (C := Pi (ded (eqT (Pi A B) f g))
        (Pi (ded (eqT A (liftN 1 0 x) (liftN 1 0 y)))
          (ded (eqT B (.app (liftN 2 0 f) (liftN 2 0 x)) (.app (liftN 2 0 g) (liftN 2 0 y))))))
    h5 hy (by simp [inst, ded, eqT, inst_closed hAc, inst_closed hBc, inst_liftN_succ, liftN_zero])
  have h7 := appE' (C := Pi (ded (eqT A x y))
          (ded (eqT B (.app (liftN 1 0 f) (liftN 1 0 x)) (.app (liftN 1 0 g) (liftN 1 0 y)))))
    h6 hp (by simp [inst, ded, eqT, inst_closed hAc, inst_closed hBc, inst_liftN_succ, liftN_zero])
  exact appE' h7 hq
    (by simp [inst, ded, eqT, inst_closed hBc, inst_liftN_succ, liftN_zero])

end Rules

/-! ## First-order terms -/

/-- First-order terms over a signature, in curried form; variables are de Bruijn
indices. -/
inductive FOT where
  /-- A variable (de Bruijn index). -/
  | var (i : Nat)
  /-- An operation symbol. -/
  | cnst (g : String)
  /-- Application. -/
  | app (f x : FOT)
deriving DecidableEq, Repr

/-- `WS Sg ctx t as b`: in a context of variable sorts `ctx` (`var i` has sort
`ctx[i]`), `t` has profile `as → b` (a fully applied term has `as = []`). -/
inductive WS (Sg : FOSig) (ctx : List String) : FOT → List String → String → Prop where
  /-- A variable has its sort in the context. -/
  | var {i s} : ctx[i]? = some s → WS Sg ctx (.var i) [] s
  /-- An operation has its profile. -/
  | cnst {g as b} : Sg.op? g = some (as, b) → WS Sg ctx (.cnst g) as b
  /-- Application consumes the first argument sort. -/
  | app {f x a as b} : WS Sg ctx f (a :: as) b → WS Sg ctx x [] a → WS Sg ctx (.app f x) as b

/-- The profile of a term, computed. -/
def prof (Sg : FOSig) (ctx : List String) : FOT → Option (List String × String)
  | .var i => ctx[i]?.map fun s => ([], s)
  | .cnst g => Sg.op? g
  | .app f x =>
    match prof Sg ctx f, prof Sg ctx x with
    | some (a :: as, b), some ([], a') => if a = a' then some (as, b) else none
    | _, _ => none

theorem WS.prof {Sg : FOSig} {ctx : List String} {t : FOT} {as : List String} {b : String}
    (h : WS Sg ctx t as b) : prof Sg ctx t = some (as, b) := by
  induction h with
  | var h => simp [MMT.Hom.prof, h]
  | cnst h => exact h
  | app _ _ ihf ihx => simp [MMT.Hom.prof, ihf, ihx]

/-- The result sort of a term. -/
def sortOf (Sg : FOSig) (ctx : List String) (t : FOT) : String :=
  ((prof Sg ctx t).map (·.2)).getD ""

theorem WS.sortOf {Sg : FOSig} {ctx : List String} {t : FOT} {as : List String} {b : String}
    (h : WS Sg ctx t as b) : sortOf Sg ctx t = b := by
  simp [MMT.Hom.sortOf, h.prof]

variable (H : ThyName) (Sg : FOSig) (ctx : List String)

/-- Encoding of first-order terms in copy `k`, with a valuation `ρ` for the variables. -/
def enc (k : String) (ρ : Nat → Term) : FOT → Term
  | .var i => ρ i
  | .cnst g => cs H k Sg g
  | .app f x => .app (enc k ρ f) (enc k ρ x)

/-- `t¹`: the encoding in copy 1, variables kept. -/
def enc1 (t : FOT) : Term := enc H Sg "1" Term.var t

/-- The valuation `xᵢ ↦ h(xᵢ)`. -/
def valH (i : Nat) : Term := .app (cs H "h" Sg ((ctx[i]?).getD "")) (.var i)

/-- `t²[h x⃗]`: the encoding in copy 2 with every variable `x` replaced by `h(x)`. -/
def encH (t : FOT) : Term := enc H Sg "2" (valH H Sg ctx) t

/-- The intermediate term `g² (h u₁¹) … (h uₘ¹)` for a spine `g u₁ … uₘ`. -/
def mixed : FOT → Term
  | .var i => valH H Sg ctx i
  | .cnst g => cs H "2" Sg g
  | .app f x => .app (mixed f) (.app (cs H "h" Sg (sortOf Sg ctx x)) (enc1 H Sg x))

/-- The head symbol of a spine. -/
def head : FOT → Option String
  | .var _ => none
  | .cnst g => some g
  | .app f _ => head f

/-- The arguments of a spine. -/
def spineArgs : FOT → List FOT
  | .app f x => spineArgs f ++ [x]
  | _ => []

/-- The instance `g^h u₁¹ … uₘ¹` of a homomorphism axiom, for a spine `g u₁ … uₘ`. -/
def axInst (t : FOT) : Term :=
  apps (cs H "h" Sg ((head t).getD "")) ((spineArgs t).map (enc1 H Sg))

/-- The full proof for a term `t : b`, given the spine proof `sp`:
`h_b(t¹) = t²[h x⃗]`. -/
def fullP (t : FOT) (sp : Term) : Term :=
  match t with
  | .var i => reflP (cs H "2" Sg ((ctx[i]?).getD "")) (valH H Sg ctx i)
  | _ =>
    let b := sortOf Sg ctx t
    transP (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (mixed H Sg ctx t)
      (encH H Sg ctx t) (axInst H Sg t) sp

/-- The spine proof for `t : as → b`: `mixed t = t²[h x⃗]` at type `as² → b²`. -/
def spineP : FOT → Term
  | .var i => reflP (cs H "2" Sg ((ctx[i]?).getD "")) (valH H Sg ctx i)
  | .cnst g =>
    match Sg.op? g with
    | some (as, b) => reflP (arrows (as.map (cs H "2" Sg)) (cs H "2" Sg b)) (cs H "2" Sg g)
    | none => .var 0
  | .app f x =>
    match prof Sg ctx f with
    | some (a :: as, b) =>
      congP (cs H "2" Sg a) (arrows (as.map (cs H "2" Sg)) (cs H "2" Sg b))
        (mixed H Sg ctx f) (encH H Sg ctx f)
        (.app (cs H "h" Sg a) (enc1 H Sg x)) (encH H Sg ctx x)
        (spineP f) (fullP H Sg ctx x (spineP x))
    | _ => .var 0

/-- The proof `P(t) : ded (h_b (t¹) = t²[h x⃗])`. -/
def proofP (t : FOT) : Term := fullP H Sg ctx t (spineP H Sg ctx t)

/-! ## Typing of the proofs -/

variable {H Sg ctx}

/-- Well-sorted argument lists. -/
inductive AllWS (Sg : FOSig) (ctx : List String) : List FOT → List String → Prop where
  /-- The empty list. -/
  | nil : AllWS Sg ctx [] []
  /-- A well-sorted term followed by well-sorted terms. -/
  | cons {u a us as} : WS Sg ctx u [] a → AllWS Sg ctx us as → AllWS Sg ctx (u :: us) (a :: as)

theorem AllWS.append {us vs : List FOT} {as bs : List String} (h1 : AllWS Sg ctx us as)
    (h2 : AllWS Sg ctx vs bs) : AllWS Sg ctx (us ++ vs) (as ++ bs) := by
  induction h1 with
  | nil => exact h2
  | cons hu _ ih => exact .cons hu ih

/-- Every non-variable term is a spine `g u₁ … uₘ` of a fully applied prefix. -/
theorem WS.spine {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (∃ i, t = .var i) ∨
    (∃ g pre, head t = some g ∧ Sg.op? g = some (pre ++ as, b) ∧ AllWS Sg ctx (spineArgs t) pre) := by
  induction h with
  | var _ => exact .inl ⟨_, rfl⟩
  | @cnst g as b hg => exact .inr ⟨g, [], rfl, by simpa using hg, .nil⟩
  | @app f x a as b hf hx ihf _ =>
    rcases ihf with ⟨i, rfl⟩ | ⟨g, pre, hh, hg, hargs⟩
    · cases hf
    · refine .inr ⟨g, pre ++ [a], hh, by simpa using hg, ?_⟩
      exact hargs.append (.cons hx .nil)

theorem apps_append (F : Term) (l : List Term) (x : Term) :
    apps F (l ++ [x]) = .app (apps F l) x := by
  induction l generalizing F with
  | nil => rfl
  | cons a l ih => simp [apps, ih]

theorem enc_spine {k : String} {ρ : Nat → Term} {t : FOT} {g : String} (h : head t = some g) :
    enc H Sg k ρ t = apps (cs H k Sg g) ((spineArgs t).map (enc H Sg k ρ)) := by
  induction t with
  | var => cases h
  | cnst g' => cases h; rfl
  | app f x ihf _ => simp [enc, spineArgs, head] at h ⊢; rw [ihf h, apps_append]

theorem mixed_spine {t : FOT} {g : String} (h : head t = some g) :
    mixed H Sg ctx t = apps (cs H "2" Sg g)
      ((spineArgs t).map fun u => .app (cs H "h" Sg (sortOf Sg ctx u)) (enc1 H Sg u)) := by
  induction t with
  | var => cases h
  | cnst g' => cases h; rfl
  | app f x ihf _ => simp [mixed, spineArgs, head] at h ⊢; rw [ihf h, apps_append]

/-- `h_{a₁} u₁, …, h_{aₙ} uₙ`. -/
def zipH (H : ThyName) (Sg : FOSig) : List String → List Term → List Term
  | a :: as, u :: us => .app (cs H "h" Sg a) u :: zipH H Sg as us
  | _, _ => []

theorem args_eq_varsDesc (as : List String) : args as = varsDesc as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [args, varsDesc, ih]

theorem substTele_cs (us : List Term) (k : String) (n : String) :
    substTele us (cs H k Sg n) = cs H k Sg n := substTele_const _ _

theorem hargs_substTele (us : List Term) (pre : List String) :
    (hargs H Sg pre).map (substTele us) =
      zipH H Sg pre ((varsDesc pre.length).map (substTele us)) := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [hargs, varsDesc, zipH, substTele_app, substTele_cs, ih]

theorem zipH_map {us : List FOT} {pre : List String} (h : AllWS Sg ctx us pre) :
    zipH H Sg pre (us.map (enc1 H Sg)) =
      us.map fun u => .app (cs H "h" Sg (sortOf Sg ctx u)) (enc1 H Sg u) := by
  induction h with
  | nil => rfl
  | cons hu _ ih => simp [zipH, ih, hu.sortOf]

theorem arr_closed (as : List String) (k b : String) :
    (arrows (as.map (cs H k Sg)) (cs H k Sg b)).ClosedAt 0 :=
  arrows_closed (fun a ha => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial) trivial

/-- Typing of encodings, for any well-typed valuation. -/
theorem enc_typed' {Γ : Ctx} {k : String} (hk : k = "1" ∨ k = "2") {ρ : Nat → Term}
    (hρ : ∀ i s, ctx[i]? = some s → D (homSig H Sg) (.typing Γ (ρ i) (cs H k Sg s)))
    {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg) (.typing Γ (enc H Sg k ρ t) (arrows (as.map (cs H k Sg)) (cs H k Sg b))) := by
  induction h with
  | var h => exact hρ _ _ h
  | cnst hg => exact op_typed hk hg Γ
  | @app f x a as b _ _ ihf ihx =>
    exact appE' ihf ihx (inst_closed (arr_closed (H := H) (Sg := Sg) as k b))

section Typing
set_option linter.unusedSectionVars false

variable (hH : H ≠ sfol)
  {Γ : Ctx} (hΓ : ∀ (i : Nat) (s : String), ctx[i]? = some s → Γ[i]? = some (cs H "1" Sg s))
  (hctx : ∀ (i : Nat) (s : String), ctx[i]? = some s → Sg.isSort s = true)
include hH hΓ hctx

theorem hS_of : ∀ c, c.thy = sfol → homSig H Sg c = metaSig c :=
  fun c hc => homSig_meta (by rw [hc]; exact Ne.symm hH)

theorem WS.sorts {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (∀ a ∈ as, Sg.isSort a = true) ∧ Sg.isSort b = true := by
  induction h with
  | var h => exact ⟨by simp, hctx _ _ h⟩
  | @cnst g as b hg => exact Sg.op_sorts g as b hg
  | app _ _ ihf _ => exact ⟨fun a ha => ihf.1 a (by simp [ha]), ihf.2⟩

theorem var_typed {i : Nat} {s : String} (h : ctx[i]? = some s) :
    D (homSig H Sg) (.typing Γ (.var i) (cs H "1" Sg s)) :=
  r0 (LF.Rule.var Γ i _ (hΓ i s h))

theorem valH_typed {i : Nat} {s : String} (h : ctx[i]? = some s) :
    D (homSig H Sg) (.typing Γ (valH H Sg ctx i) (cs H "2" Sg s)) := by
  unfold valH; rw [h]
  exact appE' (hom_typed (hctx _ _ h) Γ) (var_typed hH hΓ hctx h) rfl

theorem sorts_typed {as : List String} (has : ∀ a ∈ as, Sg.isSort a = true) {k : String}
    (hk : k = "1" ∨ k = "2") : ∀ a ∈ as.map (cs H k Sg), ∀ Γ', D (homSig H Sg) (.typing Γ' a type) := by
  intro a ha Γ'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact sort_typed hk (has x hx) Γ'

theorem arr_typed {as : List String} {b : String} (has : ∀ a ∈ as, Sg.isSort a = true)
    (hb : Sg.isSort b = true) {k : String} (hk : k = "1" ∨ k = "2") (Γ' : Ctx) :
    D (homSig H Sg) (.typing Γ' (arrows (as.map (cs H k Sg)) (cs H k Sg b)) type) :=
  arrows_typed (sorts_typed hH hΓ hctx has hk) (sort_typed hk hb _)

theorem enc_typed {k : String} (hk : k = "1" ∨ k = "2") {ρ : Nat → Term}
    (hρ : ∀ i s, ctx[i]? = some s → D (homSig H Sg) (.typing Γ (ρ i) (cs H k Sg s)))
    {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg) (.typing Γ (enc H Sg k ρ t) (arrows (as.map (cs H k Sg)) (cs H k Sg b))) := by
  induction h with
  | var h => exact hρ _ _ h
  | cnst hg => exact op_typed hk hg Γ
  | @app f x a as b _ _ ihf ihx =>
    exact appE' ihf ihx (inst_closed (arr_closed (H := H) (Sg := Sg) as k b))

theorem enc1_typed {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg) (.typing Γ (enc1 H Sg t) (arrows (as.map (cs H "1" Sg)) (cs H "1" Sg b))) :=
  enc_typed hH hΓ hctx (.inl rfl) (fun _ _ h => var_typed hH hΓ hctx h) h

theorem encH_typed {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg)
      (.typing Γ (encH H Sg ctx t) (arrows (as.map (cs H "2" Sg)) (cs H "2" Sg b))) :=
  enc_typed hH hΓ hctx (.inr rfl) (fun _ _ h => valH_typed hH hΓ hctx h) h

theorem happ_typed {x : FOT} {a : String} (hx : WS Sg ctx x [] a) :
    D (homSig H Sg) (.typing Γ (.app (cs H "h" Sg a) (enc1 H Sg x)) (cs H "2" Sg a)) :=
  appE' (hom_typed (hx.sorts hH hΓ hctx).2 Γ) (enc1_typed hH hΓ hctx hx) rfl

theorem mixed_typed {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg)
      (.typing Γ (mixed H Sg ctx t) (arrows (as.map (cs H "2" Sg)) (cs H "2" Sg b))) := by
  induction h with
  | var h => exact valH_typed hH hΓ hctx h
  | cnst hg => exact op_typed (.inr rfl) hg Γ
  | @app f x a as b _ hx ihf _ =>
    simp only [mixed, hx.sortOf]
    exact appE' ihf (happ_typed hH hΓ hctx hx) (inst_closed (arr_closed (H := H) (Sg := Sg) as "2" b))

theorem args_enc1_typed {l : List FOT} {pre : List String} (h : AllWS Sg ctx l pre) :
    Args (homSig H Sg) Γ (l.map (enc1 H Sg)) (pre.map (cs H "1" Sg)) := by
  induction h with
  | nil => exact .nil
  | cons hu _ ih => exact .cons (enc1_typed hH hΓ hctx hu) ih

/-- The instance of a homomorphism axiom at a spine. -/
theorem axInst_typed {t : FOT} {b g : String} {pre : List String} (_h : WS Sg ctx t [] b)
    (hh : head t = some g) (hg : Sg.op? g = some (pre, b))
    (hsa : AllWS Sg ctx (spineArgs t) pre) :
    D (homSig H Sg) (.typing Γ (axInst H Sg t)
      (ded (eqT (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (mixed H Sg ctx t)))) := by
  have hax : D (homSig H Sg) (.typing Γ (cs H "h" Sg g) (homAx H Sg g pre b)) :=
    .const (c := cp H "h" Sg g) (d := none)
      (by rw [homSig_cp]; simp [homInfo, FOSig.op_not_sort hg, hg])
  have hus := args_enc1_typed hH hΓ hctx hsa
  have hlen : ((spineArgs t).map (enc1 H Sg)).length = pre.length := by
    have := hus.length_eq; simpa using this
  have := apps_typed_dep hax
    (fun a ha => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial) hus
  have e : substTele ((spineArgs t).map (enc1 H Sg))
      (ded (eqT (cs H "2" Sg b) (.app (cs H "h" Sg b) (apps (cs H "1" Sg g) (args pre)))
        (apps (cs H "2" Sg g) (Hom.hargs H Sg pre)))) =
      ded (eqT (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (mixed H Sg ctx t)) := by
    simp only [ded, eqT, substTele_app, substTele_const, substTele_cs, substTele_apps,
      args_eq_varsDesc, hargs_substTele]
    rw [← hlen, substTele_varsDesc, zipH_map hsa, mixed_spine hh]
    unfold enc1; rw [enc_spine hh]
  rw [e] at this
  unfold axInst; rw [hh]
  exact this

theorem fullP_typed {t : FOT} {b : String} (h : WS Sg ctx t [] b)
    (hsp : D (homSig H Sg) (.typing Γ (spineP H Sg ctx t)
      (ded (eqT (cs H "2" Sg b) (mixed H Sg ctx t) (encH H Sg ctx t))))) :
    D (homSig H Sg) (.typing Γ (fullP H Sg ctx t (spineP H Sg ctx t))
      (ded (eqT (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (encH H Sg ctx t)))) := by
  have hb := (h.sorts hH hΓ hctx).2
  rcases h.spine with ⟨i, rfl⟩ | ⟨g, pre, hh, hg, hargs⟩
  · cases h with
    | var hi =>
      simp only [fullP, encH, enc, enc1, hi, Option.getD_some]
      have hv := valH_typed hH hΓ hctx hi
      have := refl_typed (hS_of hH hΓ hctx) (sort_typed (.inr rfl) hb Γ) trivial hv
      unfold valH at this ⊢; rw [hi] at this ⊢; exact this
  · have hfull : fullP H Sg ctx t (spineP H Sg ctx t) =
        transP (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (mixed H Sg ctx t)
          (encH H Sg ctx t) (axInst H Sg t) (spineP H Sg ctx t) := by
      cases t with
      | var => cases hh
      | cnst => simp [fullP, h.sortOf]
      | app => simp [fullP, h.sortOf]
    rw [hfull]
    simp only [List.append_nil] at hg
    exact trans_typed (hS_of hH hΓ hctx) (sort_typed (.inr rfl) hb Γ) trivial
      (appE' (hom_typed hb Γ) (enc1_typed hH hΓ hctx h) rfl)
      (mixed_typed hH hΓ hctx h) (encH_typed hH hΓ hctx h)
      (axInst_typed hH hΓ hctx h hh hg hargs) hsp

/-- **Typing of the spine proofs.** -/
theorem spineP_typed {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    D (homSig H Sg) (.typing Γ (spineP H Sg ctx t)
      (ded (eqT (arrows (as.map (cs H "2" Sg)) (cs H "2" Sg b))
        (mixed H Sg ctx t) (encH H Sg ctx t)))) := by
  induction h with
  | @var i s hi =>
    simp only [spineP, mixed, encH, enc, hi, Option.getD_some]
    exact refl_typed (hS_of hH hΓ hctx) (sort_typed (.inr rfl) (hctx _ _ hi) Γ) trivial
      (by have := valH_typed hH hΓ hctx hi; unfold valH at this ⊢; rw [hi] at this ⊢; exact this)
  | @cnst g as b hg =>
    simp only [spineP, hg, mixed, encH, enc]
    obtain ⟨has, hb⟩ := Sg.op_sorts g as b hg
    exact refl_typed (hS_of hH hΓ hctx) (arr_typed hH hΓ hctx has hb (.inr rfl) Γ)
      (arr_closed (H := H) (Sg := Sg) as "2" b) (op_typed (.inr rfl) hg Γ)
  | @app f x a as b hf hx ihf ihx =>
    simp only [spineP, hf.prof]
    obtain ⟨has, hb⟩ := hf.sorts hH hΓ hctx
    have ha : Sg.isSort a = true := has a (by simp)
    have has' : ∀ a ∈ as, Sg.isSort a = true := fun a' h' => has a' (by simp [h'])
    have := cong_typed (hS_of hH hΓ hctx) (sort_typed (.inr rfl) ha Γ)
      (arr_typed hH hΓ hctx has' hb (.inr rfl) Γ) trivial (arr_closed (H := H) (Sg := Sg) as "2" b)
      (mixed_typed hH hΓ hctx hf) (encH_typed hH hΓ hctx hf)
      (happ_typed hH hΓ hctx hx) (encH_typed hH hΓ hctx hx) ihf
      (fullP_typed hH hΓ hctx hx (by simpa [arrows] using ihx))
    simpa [mixed, encH, enc, hx.sortOf] using this

/-- **Typing of `P(t)`**: `P(t) : ded (h_b (t¹) = t²[h x⃗])`. -/
theorem proofP_typed {t : FOT} {b : String} (h : WS Sg ctx t [] b) :
    D (homSig H Sg) (.typing Γ (proofP H Sg ctx t)
      (ded (eqT (cs H "2" Sg b) (.app (cs H "h" Sg b) (enc1 H Sg t)) (encH H Sg ctx t)))) :=
  fullP_typed hH hΓ hctx h (by simpa [arrows] using spineP_typed hH hΓ hctx h)

end Typing

/-! ## Multi-step β-reduction -/

/-- `λ x₁:A₁ … xₙ:Aₙ. t` -/
def lams : List Term → Term → Term
  | [], t => t
  | A :: As, t => lam A (lams As t)

theorem inst_lams {As : List Term} (hAs : ∀ a ∈ As, a.ClosedAt 0) (j : Nat) (x t : Term) :
    inst j x (lams As t) = lams As (inst (j + As.length) x t) := by
  induction As generalizing j with
  | nil => rfl
  | cons a As ih =>
    simp only [lams, inst, List.length_cons]
    rw [inst_closed (hAs a (by simp)), ih (fun x hx => hAs x (by simp [hx]))]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem lams_typed {S : Sig} {Γ : Ctx} {As : List Term} {t T : Term}
    (hAs : ∀ a ∈ As, ∀ Γ', D S (.typing Γ' a type))
    (ht : D S (.typing (As.reverse ++ Γ) t T)) : D S (.typing Γ (lams As t) (arrows As T)) := by
  induction As generalizing Γ with
  | nil => simpa [lams, arrows] using ht
  | cons a As ih =>
    exact r2 (LF.Rule.lamI Γ a (arrows As T) (lams As t)) (hAs a (by simp) Γ)
      (ih (fun x hx => hAs x (by simp [hx])) (by simpa using ht))

theorem r1 {S : Sig} {p j} (h : LF.Rule [p] j) (hp : D S p) : D S j := .rule h (by simpa using hp)

/-- Congruence of `apps` in the head. -/
theorem apps_cong {S : Sig} {Γ : Ctx} {F F' T : Term} {us Ts : List Term}
    (hF : D S (.equal Γ F F' (arrows Ts T))) (hus : Args S Γ us Ts)
    (hTs : ∀ a ∈ Ts, a.ClosedAt 0) (hT : T.ClosedAt 0) :
    D S (.equal Γ (apps F us) (apps F' us) T) := by
  induction hus generalizing F F' with
  | nil => exact hF
  | @cons x A xs As hx _ ih =>
    have h := r2 (LF.Rule.appCong Γ A (arrows As T) F F' x x) hF (r1 (LF.Rule.refl Γ x A) hx)
    rw [inst_closed (arrows_closed (fun a ha => hTs a (by simp [ha])) hT)] at h
    exact ih h (fun a ha => hTs a (by simp [ha]))

/-- Variable-like terms: a variable, or a homomorphism symbol applied to a variable that
lies beyond the first `m` binders. -/
inductive Atom (H : ThyName) (Sg : FOSig) (C : Ctx) (m : Nat) : Term → Term → Prop where
  /-- A variable whose context entry is the copy `sᵏ`. -/
  | var {j : Nat} {k s : String} : C[j]? = some (cs H k Sg s) →
      Atom H Sg C m (.var j) (cs H k Sg s)
  /-- `h_a` applied to a variable beyond the first `m` binders. -/
  | happ {j : Nat} {a : String} : C[j]? = some (cs H "1" Sg a) → m ≤ j → Sg.isSort a = true →
      Atom H Sg C m (.app (cs H "h" Sg a) (.var j)) (cs H "2" Sg a)

theorem Atom.typed {C : Ctx} {m : Nat} {x T : Term} (h : Atom H Sg C m x T) :
    D (homSig H Sg) (.typing C x T) := by
  cases h with
  | var hj => exact r0 (LF.Rule.var C _ _ hj)
  | happ hj _ ha => exact appE' (hom_typed ha C) (r0 (LF.Rule.var C _ _ hj)) rfl

theorem getElem?_rev_append_left {Bs Γ : List Term} {j : Nat} (h : j < Bs.length) :
    (Bs.reverse ++ Γ)[j]? = Bs.reverse[j]? := by
  rw [List.getElem?_append_left (by simpa using h)]

/-- Atoms survive substituting for the outermost of the binders. -/
theorem Atom.subst {Bs : List Term} {Γ : Ctx} {B : Term} {x T u : Term}
    (hx : Atom H Sg (Bs.reverse ++ B :: Γ) (Bs.length + 1) x T ∨
      (Atom H Sg (Bs.reverse ++ B :: Γ) 0 x T ∧ ∃ j, x = .var j))
    (hu : Atom H Sg Γ 0 u B) :
    Atom H Sg (Bs.reverse ++ Γ) Bs.length (Term.inst Bs.length u x) T := by
  have hlen : Bs.reverse.length = Bs.length := by simp
  -- variables
  have hvar : ∀ j k s, (Bs.reverse ++ B :: Γ)[j]? = some (cs H k Sg s) →
      Atom H Sg (Bs.reverse ++ Γ) Bs.length (Term.inst Bs.length u (.var j)) (cs H k Sg s) := by
    intro j k s hj
    rcases Nat.lt_trichotomy j Bs.length with hl | rfl | hg
    · simp only [MMT.Term.inst, hl, ↓reduceIte]
      rw [List.getElem?_append_left (by omega)] at hj
      exact .var (by rw [List.getElem?_append_left (by omega)]; exact hj)
    · simp only [MMT.Term.inst, Nat.lt_irrefl, ↓reduceIte]
      rw [List.getElem?_append_right (by omega)] at hj
      simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      cases hu with
      | @var j' k' s' hj' =>
        simp only [liftN, Nat.not_lt_zero, ↓reduceIte]
        exact .var (by rw [List.getElem?_append_right (by omega)]; simpa [hlen] using hj')
      | @happ j' a hj' _ ha =>
        simp only [liftN, Nat.not_lt_zero, ↓reduceIte, cs]
        exact .happ (by rw [List.getElem?_append_right (by omega)]; simpa [hlen] using hj')
          (by omega) ha
    · have h1 : ¬ j < Bs.length := by omega
      have h2 : ¬ j = Bs.length := by omega
      simp only [MMT.Term.inst, h1, h2, ↓reduceIte]
      rw [List.getElem?_append_right (by omega)] at hj
      refine .var ?_
      rw [List.getElem?_append_right (by omega)]
      have : j - Bs.reverse.length = (j - 1 - Bs.reverse.length) + 1 := by simp; omega
      rw [this, List.getElem?_cons_succ] at hj
      simpa [hlen, show j - 1 - Bs.length = j - Bs.length - 1 by omega] using hj
  rcases hx with hx | ⟨hx, j, rfl⟩
  · cases hx with
    | var hj => exact hvar _ _ _ hj
    | @happ j a hj hm ha =>
      have h1 : ¬ j < Bs.length := by omega
      have h2 : ¬ j = Bs.length := by omega
      simp only [MMT.Term.inst, h1, h2, ↓reduceIte, cs]
      refine .happ ?_ (by omega) ha
      rw [List.getElem?_append_right (by omega)] at hj
      rw [List.getElem?_append_right (by omega)]
      have : j - Bs.reverse.length = (j - 1 - Bs.reverse.length) + 1 := by simp; omega
      rw [this, List.getElem?_cons_succ] at hj
      simpa [hlen, show j - 1 - Bs.length = j - Bs.length - 1 by omega] using hj
  · cases hx with
    | var hj => exact hvar _ _ _ hj

/-- Atom-typed argument lists. -/
inductive AtomArgs (H : ThyName) (Sg : FOSig) (Γ : Ctx) : List Term → List Term → Prop where
  /-- The empty list. -/
  | nil : AtomArgs H Sg Γ [] []
  /-- An atom followed by atoms. -/
  | cons {u T us Ts} : Atom H Sg Γ 0 u T → AtomArgs H Sg Γ us Ts →
      AtomArgs H Sg Γ (u :: us) (T :: Ts)

theorem AtomArgs.args {Γ : Ctx} {us Ts : List Term} (h : AtomArgs H Sg Γ us Ts) :
    Args (homSig H Sg) Γ us Ts := by
  induction h with
  | nil => exact .nil
  | cons hu _ ih => exact .cons hu.typed ih

theorem AtomArgs.length_eq {Γ : Ctx} {us Ts : List Term} (h : AtomArgs H Sg Γ us Ts) :
    us.length = Ts.length := h.args.length_eq

theorem inst_enc (j : Nat) (u : Term) (k : String) (ρ : Nat → Term) (t : FOT) :
    Term.inst j u (enc H Sg k ρ t) = enc H Sg k (fun i => Term.inst j u (ρ i)) t := by
  induction t with
  | var => rfl
  | cnst => rfl
  | app f x ihf ihx => simp [enc, Term.inst, ihf, ihx]

theorem enc_congr {k : String} {ρ ρ' : Nat → Term} {ctx : List String} {t : FOT}
    {as : List String} {b : String} (h : WS Sg ctx t as b)
    (hρ : ∀ i s, ctx[i]? = some s → ρ i = ρ' i) : enc H Sg k ρ t = enc H Sg k ρ' t := by
  induction h with
  | var hi => exact hρ _ _ hi
  | cnst => rfl
  | app _ _ ihf ihx => simp [enc, ihf, ihx]

theorem cs_closed (k n : String) : (cs H k Sg n).ClosedAt 0 := trivial

/-- **Multi-step β-reduction** of `(λ x⃗:B⃗ᵏ. tᵏ[ρ]) u⃗` for atom arguments `u⃗`. -/
theorem multiBeta {k : String} (hk : k = "1" ∨ k = "2") {ctx : List String} {t : FOT}
    {b : String} (ht : WS Sg ctx t [] b) (Γ : Ctx) :
    ∀ (Bs : List String) (ρ : Nat → Term) (us : List Term),
      (∀ B ∈ Bs, Sg.isSort B = true) →
      (∀ i s, ctx[i]? = some s →
        Atom H Sg ((Bs.map (cs H k Sg)).reverse ++ Γ) Bs.length (ρ i) (cs H k Sg s)) →
      AtomArgs H Sg Γ us (Bs.map (cs H k Sg)) →
      D (homSig H Sg) (.equal Γ (apps (lams (Bs.map (cs H k Sg)) (enc H Sg k ρ t)) us)
        (enc H Sg k (fun i => substTele us (ρ i)) t) (cs H k Sg b))
  | [], ρ, us, _, hρ, hus => by
    cases hus
    have := enc_typed' (H := H) (Sg := Sg) hk (fun i s h => (hρ i s h).typed) ht
    simpa [lams, apps, substTele, arrows] using r1 (LF.Rule.refl Γ _ _) this
  | B :: Bs, ρ, us, hBs, hρ, hus => by
    cases hus with
    | @cons u T us' Ts hu hus' =>
      have hB : Sg.isSort B = true := hBs B (by simp)
      have hBs' : ∀ B ∈ Bs, Sg.isSort B = true := fun B' h => hBs B' (by simp [h])
      set_option linter.unusedVariables false in
      have hlen : (Bs.map (cs H k Sg)).length = Bs.length := by simp
      have hsorts : ∀ a ∈ Bs.map (cs H k Sg), ∀ Γ', D (homSig H Sg) (.typing Γ' a type) := by
        intro a ha Γ'
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        exact sort_typed hk (hBs' x hx) Γ'
      have hcl : ∀ a ∈ Bs.map (cs H k Sg), a.ClosedAt 0 := by
        intro a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial
      -- the body is typed in the current context
      have hctxeq : ((B :: Bs).map (cs H k Sg)).reverse ++ Γ =
          (Bs.map (cs H k Sg)).reverse ++ (cs H k Sg B :: Γ) := by simp
      have hE : D (homSig H Sg) (.typing ((Bs.map (cs H k Sg)).reverse ++ (cs H k Sg B :: Γ))
          (enc H Sg k ρ t) (cs H k Sg b)) := by
        have := enc_typed' (H := H) (Sg := Sg) hk (fun i s h => (hρ i s h).typed) ht
        simpa [hctxeq, arrows] using this
      -- one β-step
      have hβ := r2 (LF.Rule.beta Γ (cs H k Sg B) (arrows (Bs.map (cs H k Sg)) (cs H k Sg b))
        (lams (Bs.map (cs H k Sg)) (enc H Sg k ρ t)) u)
        (lams_typed hsorts hE) hu.typed
      rw [inst_closed (arrows_closed hcl (cs_closed _ _)), inst_lams hcl, inst_enc] at hβ
      simp only [Nat.zero_add, hlen] at hβ
      -- propagate through the remaining arguments
      have hβ' := apps_cong hβ hus'.args hcl (cs_closed _ _)
      -- the rest, by induction
      have hρ' : ∀ i s, ctx[i]? = some s →
          Atom H Sg ((Bs.map (cs H k Sg)).reverse ++ Γ) Bs.length
            (Term.inst Bs.length u (ρ i)) (cs H k Sg s) := by
        intro i s hi
        have := Atom.subst (Bs := Bs.map (cs H k Sg)) (Γ := Γ) (B := cs H k Sg B)
          (.inl (by have h' := hρ i s hi; rw [hctxeq] at h'; simpa [hlen] using h')) hu
        simpa [hlen] using this
      have ih := multiBeta hk ht Γ Bs (fun i => Term.inst Bs.length u (ρ i)) us' hBs' hρ' hus'
      have hlen' : us'.length = Bs.length := by simpa using hus'.length_eq
      have := r2 (LF.Rule.trans Γ _ _ _ _) hβ' ih
      simpa [lams, apps, substTele, hlen'] using this

/-! ## Instantiating telescopes at variables -/

theorem substTele_liftN : ∀ (us : List Term) (x : Term), substTele us (liftN us.length 0 x) = x
  | [], x => by simp [substTele, liftN_zero]
  | u :: us, x => by
    simp only [substTele, List.length_cons]
    rw [inst_liftN_succ]; exact substTele_liftN us x

theorem substTele_var_lt : ∀ (us : List Term) (i : Nat), i < us.length →
    some (substTele us (.var i)) = us[us.length - 1 - i]?
  | [], _, h => by simp at h
  | u :: us, i, h => by
    simp only [substTele, List.length_cons] at h ⊢
    by_cases hi : i < us.length
    · simp only [Term.inst, hi, ↓reduceIte]
      rw [substTele_var_lt us i hi]
      have : us.length + 1 - 1 - i = (us.length - 1 - i) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
    · have : i = us.length := by omega
      subst this
      simp [Term.inst, substTele_liftN]

theorem varsDesc_getElem? : ∀ (n p : Nat), p < n → (varsDesc n)[p]? = some (.var (n - 1 - p))
  | 0, _, h => by simp at h
  | n + 1, 0, _ => by simp [varsDesc]
  | n + 1, p + 1, h => by
    simp only [varsDesc, List.getElem?_cons_succ]
    rw [varsDesc_getElem? n p (by omega)]; congr 2; omega

theorem hargs_getElem? (As : List String) : ∀ p, p < As.length →
    (Hom.hargs H Sg As)[p]? =
      As[p]?.map fun a => .app (cs H "h" Sg a) (.var (As.length - 1 - p)) := by
  induction As with
  | nil => intro p h; simp at h
  | cons a rest ih =>
    intro p hp
    cases p with
    | zero => simp [Hom.hargs]
    | succ p =>
      simp only [Hom.hargs, List.getElem?_cons_succ, List.length_cons]
      rw [ih p (by simpa using hp)]
      have : rest.length - 1 - p = rest.length + 1 - 1 - (p + 1) := by omega
      rw [this]

theorem hargs_length (As : List String) : (Hom.hargs H Sg As).length = As.length := by
  induction As with
  | nil => rfl
  | cons a As ih => simp [Hom.hargs, ih]

/-! ## The two β-reductions in the translated axiom -/

section Beta

variable {As : List String} (hAs : ∀ a ∈ As, Sg.isSort a = true)
include hAs

theorem atomArgs_vars (Γ₀ : Ctx) :
    AtomArgs H Sg ((As.map (cs H "1" Sg)).reverse ++ Γ₀) (varsDesc As.length)
      (As.map (cs H "1" Sg)) := by
  induction As generalizing Γ₀ with
  | nil => exact .nil
  | cons a rest ih =>
    have e : ((a :: rest).map (cs H "1" Sg)).reverse ++ Γ₀ =
        (rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀) := by simp
    rw [e, List.length_cons, varsDesc]
    refine .cons (.var ?_) (ih (fun x hx => hAs x (by simp [hx])) _)
    rw [List.getElem?_append_right (by simp)]; simp

theorem atomArgs_hargs (Γ₀ : Ctx) :
    AtomArgs H Sg ((As.map (cs H "1" Sg)).reverse ++ Γ₀) (Hom.hargs H Sg As)
      (As.map (cs H "2" Sg)) := by
  induction As generalizing Γ₀ with
  | nil => exact .nil
  | cons a rest ih =>
    have e : ((a :: rest).map (cs H "1" Sg)).reverse ++ Γ₀ =
        (rest.map (cs H "1" Sg)).reverse ++ (cs H "1" Sg a :: Γ₀) := by simp
    rw [e]
    refine .cons (.happ ?_ (Nat.zero_le _) (hAs a (by simp)))
      (ih (fun x hx => hAs x (by simp [hx])) _)
    rw [List.getElem?_append_right (by simp)]; simp

omit hAs in
theorem ctx_lookup {k : String} {Γ₀ : Ctx} {i : Nat} {s : String} (hi : As.reverse[i]? = some s) :
    ((As.map (cs H k Sg)).reverse ++ Γ₀)[i]? = some (cs H k Sg s) := by
  have hl : i < As.length := by
    rcases Nat.lt_or_ge i As.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at hi; cases hi
  rw [List.getElem?_append_left (by simpa using hl), ← List.map_reverse, List.getElem?_map, hi]
  rfl

/-- `(λx⃗. t¹) x⃗ ≡ t¹` -/
theorem beta1 {t : FOT} {b : String} (ht : WS Sg As.reverse t [] b) :
    D (homSig H Sg) (.equal (As.map (cs H "1" Sg)).reverse
      (apps (lams (As.map (cs H "1" Sg)) (enc1 H Sg t)) (varsDesc As.length))
      (enc1 H Sg t) (cs H "1" Sg b)) := by
  have h := multiBeta (H := H) (Sg := Sg) (.inl rfl) ht (As.map (cs H "1" Sg)).reverse As Term.var
    (varsDesc As.length) hAs (fun i s hi => .var (ctx_lookup hi)) (by simpa using atomArgs_vars hAs [])
  rw [enc_congr (ρ := fun i => substTele (varsDesc As.length) (.var i)) (ρ' := Term.var) ht ?_] at h
  · exact h
  intro i s hi
  have hl : i < As.length := by
    rcases Nat.lt_or_ge i As.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at hi; cases hi
  have := substTele_var_lt (varsDesc As.length) i (by simpa [varsDesc_length] using hl)
  rw [varsDesc_length, varsDesc_getElem? _ _ (by omega)] at this
  simpa [show As.length - 1 - (As.length - 1 - i) = i by omega] using this

/-- `(λx⃗. t²) (h x⃗) ≡ t²[h x⃗]` -/
theorem betaH {t : FOT} {b : String} (ht : WS Sg As.reverse t [] b) :
    D (homSig H Sg) (.equal (As.map (cs H "1" Sg)).reverse
      (apps (lams (As.map (cs H "2" Sg)) (enc H Sg "2" Term.var t)) (Hom.hargs H Sg As))
      (encH H Sg As.reverse t) (cs H "2" Sg b)) := by
  have h := multiBeta (H := H) (Sg := Sg) (.inr rfl) ht (As.map (cs H "1" Sg)).reverse As Term.var
    (Hom.hargs H Sg As) hAs (fun i s hi => .var (ctx_lookup hi)) (by simpa using atomArgs_hargs hAs [])
  unfold encH
  rw [enc_congr (ρ := fun i => substTele (Hom.hargs H Sg As) (.var i))
    (ρ' := valH H Sg As.reverse) ht ?_] at h
  · exact h
  intro i s hi
  have hl : i < As.length := by
    rcases Nat.lt_or_ge i As.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at hi; cases hi
  have := substTele_var_lt (Hom.hargs H Sg As) i (by simpa [hargs_length] using hl)
  rw [hargs_length, hargs_getElem? _ _ (by omega)] at this
  rw [List.getElem?_reverse hl] at hi
  rw [hi] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [this]
  simp [valH, List.getElem?_reverse hl, hi, show As.length - 1 - (As.length - 1 - i) = i by omega]

end Beta

/-! ## Closedness of the image terms -/

section Closed

variable {ctx : List String} {n : Nat} (hn : ∀ i s, ctx[i]? = some s → i < n)
include hn

omit hn in
theorem apps_closedAt {F : Term} {l : List Term} (hF : F.ClosedAt n)
    (hl : ∀ x ∈ l, x.ClosedAt n) : (apps F l).ClosedAt n := by
  induction l generalizing F with
  | nil => exact hF
  | cons x l ih => exact ih ⟨hF, hl x (by simp)⟩ (fun y hy => hl y (by simp [hy]))

omit hn in
theorem cs_closedAt (k m : String) : (cs H k Sg m).ClosedAt n := trivial

omit hn in
theorem enc_closedAt {k : String} {ρ : Nat → Term} {t : FOT} {as : List String} {b : String}
    (h : WS Sg ctx t as b) (hρ : ∀ i s, ctx[i]? = some s → (ρ i).ClosedAt n) :
    (enc H Sg k ρ t).ClosedAt n := by
  induction h with
  | var hi => exact hρ _ _ hi
  | cnst => trivial
  | app _ _ ihf ihx => exact ⟨ihf, ihx⟩

theorem var_closedAt {i : Nat} {s : String} (hi : ctx[i]? = some s) : (Term.var i).ClosedAt n :=
  hn i s hi

theorem valH_closedAt {i : Nat} {s : String} (hi : ctx[i]? = some s) :
    (valH H Sg ctx i).ClosedAt n := ⟨trivial, hn i s hi⟩

theorem enc1_closedAt {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (enc1 H Sg t).ClosedAt n := enc_closedAt h (fun _ _ hi => hn _ _ hi)

theorem encH_closedAt {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (encH H Sg ctx t).ClosedAt n := enc_closedAt h (fun _ _ hi => valH_closedAt hn hi)

theorem mixed_closedAt {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (mixed H Sg ctx t).ClosedAt n := by
  induction h with
  | var hi => exact valH_closedAt hn hi
  | cnst => trivial
  | app _ hx ihf _ => exact ⟨ihf, trivial, enc1_closedAt hn hx⟩

theorem allWS_closedAt {l : List FOT} {pre : List String} (h : AllWS Sg ctx l pre) :
    ∀ x ∈ l.map (enc1 H Sg), x.ClosedAt n := by
  induction h with
  | nil => simp
  | cons hu _ ih =>
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact enc1_closedAt hn hu
    · exact ih x hx

theorem fullP_closedAt {t : FOT} {b : String} (h : WS Sg ctx t [] b) {sp : Term}
    (hsp : sp.ClosedAt n) : (fullP H Sg ctx t sp).ClosedAt n := by
  rcases h.spine with ⟨i, rfl⟩ | ⟨g, pre, hh, hg, hsa⟩
  · cases h with
    | var hi => exact ⟨⟨trivial, trivial⟩, valH_closedAt hn hi⟩
  · have hax : (axInst H Sg t).ClosedAt n := by
      unfold axInst; exact apps_closedAt (by trivial) (allWS_closedAt hn hsa)
    have : fullP H Sg ctx t sp = transP (cs H "2" Sg (sortOf Sg ctx t))
        (.app (cs H "h" Sg (sortOf Sg ctx t)) (enc1 H Sg t)) (mixed H Sg ctx t)
        (encH H Sg ctx t) (axInst H Sg t) sp := by
      cases t with
      | var => cases hh
      | cnst => rfl
      | app => rfl
    rw [this]
    unfold transP
    refine apps_closedAt (by trivial) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact ⟨trivial, enc1_closedAt hn h⟩
    · exact mixed_closedAt hn h
    · exact encH_closedAt hn h
    · exact hax
    · exact hsp

theorem spineP_closedAt {t : FOT} {as : List String} {b : String} (h : WS Sg ctx t as b) :
    (spineP H Sg ctx t).ClosedAt n := by
  induction h with
  | var hi => exact ⟨⟨trivial, trivial⟩, valH_closedAt hn hi⟩
  | @cnst g as b hg =>
    simp only [spineP, hg]
    exact ⟨⟨trivial, (arr_closed (H := H) (Sg := Sg) as "2" b).mono (Nat.zero_le _)⟩, trivial⟩
  | @app f x a as b hf hx ihf ihx =>
    simp only [spineP, hf.prof]
    unfold congP
    refine apps_closedAt (by trivial) ?_
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact (arr_closed (H := H) (Sg := Sg) as "2" b).mono (Nat.zero_le _)
    · exact mixed_closedAt hn hf
    · exact encH_closedAt hn hf
    · exact ⟨trivial, enc1_closedAt hn hx⟩
    · exact encH_closedAt hn hx
    · exact ihf
    · exact fullP_closedAt hn hx ihx

theorem proofP_closedAt {t : FOT} {b : String} (h : WS Sg ctx t [] b) :
    (proofP H Sg ctx t).ClosedAt n :=
  fullP_closedAt hn h (spineP_closedAt hn h)

end Closed

theorem lams_closed {As : List Term} {t : Term} (hAs : ∀ a ∈ As, a.ClosedAt 0)
    (ht : t.ClosedAt As.length) : (lams As t).ClosedAt 0 := by
  induction As generalizing t with
  | nil => exact ht
  | cons a As ih =>
    -- `lams (a :: As) t = lam a (lams As t)`; close the inner part at depth 1
    have key : ∀ (L : List Term) (u : Term) (d : Nat), (∀ x ∈ L, x.ClosedAt 0) →
        u.ClosedAt (d + L.length) → (lams L u).ClosedAt d := by
      intro L
      induction L with
      | nil => intro u d _ hu; simpa [lams] using hu
      | cons x L ihL =>
        intro u d hL hu
        exact ⟨trivial, (hL x (by simp)).mono (Nat.zero_le _),
          ihL u (d + 1) (fun y hy => hL y (by simp [hy])) (by simpa [Nat.add_assoc, Nat.add_comm 1] using hu)⟩
    exact key (a :: As) t 0 hAs (by simpa using ht)

/-! ## The homomorphism functor on views -/

/-- A view between first-order signatures: sorts go to sorts, and an operation
`f : as → b` goes to a term over the codomain in variables `x₁ … xₙ` of sorts
`φ(as)` (de Bruijn: `xᵢ = var (n-i)`). -/
structure FOView (Sg Sg' : FOSig) where
  /-- The map of sorts. -/
  sort : String → String
  /-- Sorts are mapped to sorts. -/
  sortOk : ∀ n, Sg.isSort n = true → Sg'.isSort (sort n) = true
  /-- The term assigned to each operation. -/
  opT : String → FOT
  /-- Assigned terms are well-sorted at the mapped profile. -/
  opOk : ∀ f as b, Sg.op? f = some (as, b) →
    WS Sg' ((as.map sort).reverse) (opT f) [] (sort b)

namespace FOView

variable {Sg Sg' : FOSig} (μ : FOView Sg Sg') (H H' : ThyName)

/-- The image of `nᵏ` for an operation `n : as → b`. -/
def opImage (k : String) (n : String) (as : List String) : Term :=
  let As := as.map μ.sort
  if k = "1" then lams (As.map (cs H' "1" Sg')) (enc1 H' Sg' (μ.opT n))
  else if k = "2" then lams (As.map (cs H' "2" Sg')) (enc H' Sg' "2" Term.var (μ.opT n))
  else lams (As.map (cs H' "1" Sg')) (proofP H' Sg' As.reverse (μ.opT n))

/-- `Hom(φ)`: sorts and their homomorphisms are renamed; `f¹, f²` go to `λx⃗. t¹`, `λx⃗. t²`;
`f^h` goes to the proof `λx⃗. P(t)`. -/
def hom : Subst := fun d =>
  if d.thy = H then
    match d.name with
    | .sub k thy (.base n) =>
      if thy = Sg.thy then
        if Sg.isSort n then cs H' k Sg' (μ.sort n)
        else match Sg.op? n with
          | some (as, _) => if k = "1" ∨ k = "2" ∨ k = "h" then μ.opImage H' k n as else .const d
          | none => .const d
      else .const d
    | _ => .const d
  else .const d

variable {μ H H'}

theorem hom_sort {k n : String} (hs : Sg.isSort n = true) :
    μ.hom H H' (cp H k Sg n) = cs H' k Sg' (μ.sort n) := by
  simp [hom, cp, hs]

theorem hom_op {k n : String} {as : List String} {b : String} (hf : Sg.op? n = some (as, b))
    (hk : k = "1" ∨ k = "2" ∨ k = "h") :
    μ.hom H H' (cp H k Sg n) = μ.opImage H' k n as := by
  simp [hom, cp, FOSig.op_not_sort hf, hf, hk]

theorem hom_other {d : GName} (h : d.thy ≠ H) : μ.hom H H' d = .const d := by
  simp [hom, h]

/-- Every image is of one of three shapes. -/
theorem hom_cases (d : GName) :
    μ.hom H H' d = .const d ∨ (∃ k m, μ.hom H H' d = cs H' k Sg' m) ∨
    (∃ k n as b, Sg.op? n = some (as, b) ∧ μ.hom H H' d = μ.opImage H' k n as) := by
  obtain ⟨t, nm⟩ := d
  unfold hom
  by_cases ht : t = H
  · simp only [ht, ↓reduceIte]
    split
    · rename_i k thy n
      by_cases hthy : thy = Sg.thy
      · simp only [hthy, ↓reduceIte]
        by_cases hs : Sg.isSort n = true
        · simp only [hs, ↓reduceIte]; exact .inr (.inl ⟨_, _, rfl⟩)
        · simp only [Bool.not_eq_true] at hs
          simp only [hs, Bool.false_eq_true, ↓reduceIte]
          cases hf : Sg.op? n with
          | none => exact .inl rfl
          | some p =>
            obtain ⟨as, b⟩ := p
            simp only
            split
            · exact .inr (.inr ⟨k, n, as, b, hf, rfl⟩)
            · exact .inl rfl
      · simp [hthy]
    · exact .inl rfl
  · simp [ht]

theorem opImage_closed {k n : String} {as : List String} {b : String}
    (hf : Sg.op? n = some (as, b)) : (μ.opImage H' k n as).ClosedAt 0 := by
  have hws := μ.opOk n as b hf
  have hn : ∀ i s, ((as.map μ.sort).reverse)[i]? = some s → i < (as.map μ.sort).length := by
    intro i s hi
    rcases Nat.lt_or_ge i (as.map μ.sort).length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at hi; cases hi
  have hcl : ∀ k', ∀ a ∈ (as.map μ.sort).map (cs H' k' Sg'), a.ClosedAt 0 := by
    intro k' a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; trivial
  unfold opImage
  simp only
  split
  · exact lams_closed (hcl _) (by simpa using enc1_closedAt hn hws)
  · split
    · exact lams_closed (hcl _) (by simpa using enc_closedAt hws (fun _ _ hi => var_closedAt hn hi))
    · exact lams_closed (hcl _) (by simpa using proofP_closedAt hn hws)

section Main

variable (hH : H ≠ sfol) (hL : H ≠ LF.thy) (hH' : H' ≠ sfol)
include hH hL

theorem hom_fix {c : GName} (h : c.thy = sfol ∨ c.thy = LF.thy) : μ.hom H H' c = .const c := by
  apply hom_other; rcases h with h | h <;> rw [h]
  · exact Ne.symm hH
  · exact Ne.symm hL

omit hH hL in
theorem cs_sort_trans {k a : String} (ha : Sg.isSort a = true) :
    (cs H k Sg a).trans (μ.hom H H') = cs H' k Sg' (μ.sort a) := by
  simp [cs, Term.trans, hom_sort ha]

/-- The translated homomorphism axiom. -/
theorem homAx_trans {f : String} {as : List String} {b : String} (hf : Sg.op? f = some (as, b)) :
    (homAx H Sg f as b).trans (μ.hom H H') =
      arrows ((as.map μ.sort).map (cs H' "1" Sg'))
        (ded (eqT (cs H' "2" Sg' (μ.sort b))
          (.app (cs H' "h" Sg' (μ.sort b))
            (apps (μ.opImage H' "1" f as) (varsDesc (as.map μ.sort).length)))
          (apps (μ.opImage H' "2" f as) (Hom.hargs H' Sg' (as.map μ.sort))))) := by
  obtain ⟨has, hb⟩ := Sg.op_sorts f as b hf
  have hP : μ.hom H H' piN = .const piN := hom_fix hH hL (.inr rfl)
  have hD : μ.hom H H' dedN = .const dedN := hom_fix hH hL (.inl rfl)
  have hE : μ.hom H H' eqN = .const eqN := hom_fix hH hL (.inl rfl)
  have hvars : ∀ m, (varsDesc m).map (·.trans (μ.hom H H')) = varsDesc m := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => simp [varsDesc, ih, Term.trans]
  have hh : ∀ l : List String, (∀ a ∈ l, Sg.isSort a = true) →
      (Hom.hargs H Sg l).map (·.trans (μ.hom H H')) = Hom.hargs H' Sg' (l.map μ.sort) := by
    intro l hl; induction l with
    | nil => rfl
    | cons a l ih =>
      simp [Hom.hargs, Term.trans, cs_sort_trans (hl a (by simp)),
        ih (fun x hx => hl x (by simp [hx]))]
  have hmap : (as.map (cs H "1" Sg)).map (·.trans (μ.hom H H')) =
      (as.map μ.sort).map (cs H' "1" Sg') := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha; exact cs_sort_trans (has a ha)
  unfold homAx
  rw [arrows_trans hP, hmap]
  simp only [ded, eqT, Term.trans, hD, hE, cs_sort_trans hb, apps_trans, args_eq_varsDesc,
    hvars, hh as has, List.length_map]
  simp [cs, Term.trans, hom_op hf]

end Main

end FOView

/-! ## Converting the proof to the translated axiom -/

section Convert

variable {H : ThyName} {Sg : FOSig} (hH : H ≠ sfol) {As : List String}
  (hAs : ∀ a ∈ As, Sg.isSort a = true) {t : FOT} {B : String} (ht : WS Sg As.reverse t [] B)
include hH hAs ht

/-- The proof `P(t)` has the β-redex form of the translated axiom as its type. -/
theorem proofP_converted :
    D (homSig H Sg) (.typing (As.map (cs H "1" Sg)).reverse (proofP H Sg As.reverse t)
      (ded (eqT (cs H "2" Sg B)
        (.app (cs H "h" Sg B) (apps (lams (As.map (cs H "1" Sg)) (enc1 H Sg t)) (varsDesc As.length)))
        (apps (lams (As.map (cs H "2" Sg)) (enc H Sg "2" Term.var t)) (Hom.hargs H Sg As))))) := by
  set_option linter.unusedVariables false in
  have hS := hS_of (Γ := (As.map (cs H "1" Sg)).reverse) (ctx := As.reverse) hH
    (fun i s hi => by simpa using ctx_lookup (H := H) (Sg := Sg) (k := "1") (Γ₀ := []) hi)
    (fun i s hi => hAs s (List.mem_reverse.mp (List.mem_of_getElem? hi)))
  have hΓ : ∀ (i : Nat) (s : String), As.reverse[i]? = some s →
      ((As.map (cs H "1" Sg)).reverse)[i]? = some (cs H "1" Sg s) :=
    fun i s hi => by simpa using ctx_lookup (H := H) (Sg := Sg) (k := "1") (Γ₀ := []) hi
  have hctx : ∀ (i : Nat) (s : String), As.reverse[i]? = some s → Sg.isSort s = true :=
    fun i s hi => hAs s (List.mem_reverse.mp (List.mem_of_getElem? hi))
  have hB : Sg.isSort B = true := (ht.sorts hH hΓ hctx).2
  have hP := proofP_typed hH hΓ hctx ht
  let Γ := (As.map (cs H "1" Sg)).reverse
  have refl' : ∀ {x A : Term}, D (homSig H Sg) (.typing Γ x A) →
      D (homSig H Sg) (.equal Γ x x A) := fun h => r1 (LF.Rule.refl _ _ _) h
  have symm' : ∀ {x y A : Term}, D (homSig H Sg) (.equal Γ x y A) →
      D (homSig H Sg) (.equal Γ y x A) := fun h => r1 (LF.Rule.symm _ _ _ _) h
  -- the left-hand side
  have eX := r2 (LF.Rule.appCong Γ (cs H "1" Sg B) (cs H "2" Sg B) (cs H "h" Sg B)
    (cs H "h" Sg B) _ _) (refl' (hom_typed hB Γ)) (symm' (beta1 hAs ht))
  rw [inst_closed (cs_closed _ _)] at eX
  -- the right-hand side
  have eY := symm' (betaH hAs ht)
  -- `eq c`
  have heq : D (homSig H Sg) (.typing Γ (.const eqN) (Pi type (Pi (.var 0) (Pi (.var 1) prop)))) :=
    meta_typed hH (d := none) (by simp [metaSig, eqN, propN, dedN]) Γ
  have heqc : D (homSig H Sg) (.typing Γ (.app (.const eqN) (cs H "2" Sg B))
      (Pi (cs H "2" Sg B) (Pi (cs H "2" Sg B) prop))) :=
    appE' heq (sort_typed (.inr rfl) hB Γ) rfl
  have e2 := r2 (LF.Rule.appCong Γ (cs H "2" Sg B) (Pi (cs H "2" Sg B) prop) _ _ _ _)
    (refl' heqc) eX
  rw [inst_closed (by exact ⟨trivial, trivial, trivial⟩)] at e2
  have e3 := r2 (LF.Rule.appCong Γ (cs H "2" Sg B) prop _ _ _ _) e2 eY
  have hded : D (homSig H Sg) (.typing Γ (.const dedN) (Pi prop type)) :=
    meta_typed hH (d := none) (by simp [metaSig, propN, dedN]) Γ
  have e4 := r2 (LF.Rule.appCong Γ prop type _ _ _ _) (refl' hded) e3
  exact r2 (LF.Rule.conv Γ _ _ _ type) hP e4

end Convert

namespace FOView

variable {Sg Sg' : FOSig} {μ : FOView Sg Sg'} {H H' : ThyName}

/-- **The homomorphism functor on views with compound terms**: `Hom(φ)` is a well-typed
morphism `Hom(Σ) → Hom(Σ')`. -/
theorem hom_isMorphism (hH : H ≠ sfol) (hL : H ≠ LF.thy) (hH' : H' ≠ sfol) :
    IsMorphism LF.foundation (homSig H Sg) (homSig H' Sg') (μ.hom H H') where
  closed d := by
    rcases hom_cases (μ := μ) (H := H) (H' := H') d with h | ⟨k, m, h⟩ | ⟨k, n, as, b, hf, h⟩
    · rw [h]; trivial
    · rw [h]; trivial
    · rw [h]; exact opImage_closed hf
  fixMeta c hc := hom_fix hH hL (.inr hc)
  typed {c A d} hc := by
    rcases homSig_cases hc with ⟨k, n, rfl, hi⟩ | ⟨hne, hm⟩
    · have hdf := homInfo_df hi; simp only at hdf; subst hdf
      unfold homInfo at hi
      by_cases hk : k = "1" ∨ k = "2"
      · simp only [hk, ↓reduceIte] at hi
        by_cases hs : Sg.isSort n = true
        · simp only [hs, ↓reduceIte] at hi; cases hi
          rw [hom_sort hs]
          refine .const (c := cp H' k Sg' (μ.sort n)) (d := none) ?_
          rw [homSig_cp]
          simp [homInfo, hk, μ.sortOk n hs, Term.trans, hom_fix hH hL (c := typeN) (.inr rfl)]
        · simp only [hs] at hi
          obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp hi
          cases hi
          obtain ⟨has, hb⟩ := Sg.op_sorts n as b hf
          have hAs : ∀ a ∈ as.map μ.sort, Sg'.isSort a = true := by
            intro a ha; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact μ.sortOk x (has x hx)
          have hws := μ.opOk n as b hf
          have hk' : k = "1" ∨ k = "2" ∨ k = "h" := by rcases hk with h | h <;> simp [h]
          rw [hom_op hf hk', arrows_trans (hom_fix hH hL (.inr rfl)), cs_sort_trans hb]
          have hmap : (as.map (cs H k Sg)).map (·.trans (μ.hom H H')) =
              (as.map μ.sort).map (cs H' k Sg') := by
            simp only [List.map_map]; apply List.map_congr_left
            intro a ha; exact cs_sort_trans (has a ha)
          rw [hmap]
          have hsorts : ∀ a ∈ (as.map μ.sort).map (cs H' k Sg'), ∀ Γ',
              D (homSig H' Sg') (.typing Γ' a type) := by
            intro a ha Γ'; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact sort_typed hk (hAs x hx) Γ'
          have hbody := enc_typed' (H := H') (Sg := Sg') (Γ := ((as.map μ.sort).map (cs H' k Sg')).reverse ++ [])
            hk (ρ := Term.var) (fun i s hi => r0 (LF.Rule.var _ _ _ (ctx_lookup hi))) hws
          unfold opImage
          rcases hk with rfl | rfl
          · exact lams_typed hsorts (by simpa [arrows, enc1] using hbody)
          · exact lams_typed hsorts (by simpa [arrows] using hbody)
      · simp only [hk, ↓reduceIte] at hi
        by_cases hh : k = "h"
        · subst hh
          simp only [↓reduceIte] at hi
          by_cases hs : Sg.isSort n = true
          · simp only [hs, ↓reduceIte] at hi; cases hi
            rw [hom_sort hs]
            refine .const (c := cp H' "h" Sg' (μ.sort n)) (d := none) ?_
            rw [homSig_cp]
            simp [homInfo, μ.sortOk n hs, Term.trans, hom_fix hH hL (c := piN) (.inr rfl),
              cs_sort_trans hs]
          · simp only [hs] at hi
            obtain ⟨⟨as, b⟩, hf, hi⟩ := Option.map_eq_some_iff.mp hi
            cases hi
            obtain ⟨has, hb⟩ := Sg.op_sorts n as b hf
            have hAs : ∀ a ∈ as.map μ.sort, Sg'.isSort a = true := by
              intro a ha; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha; exact μ.sortOk x (has x hx)
            rw [hom_op hf (.inr (.inr rfl)), homAx_trans hH hL hf]
            have hsorts : ∀ a ∈ (as.map μ.sort).map (cs H' "1" Sg'), ∀ Γ',
                D (homSig H' Sg') (.typing Γ' a type) := by
              intro a ha Γ'; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
              exact sort_typed (.inl rfl) (hAs x hx) Γ'
            have hconv := proofP_converted hH' hAs (μ.opOk n as b hf)
            refine lams_typed hsorts ?_
            simpa [opImage] using hconv
        · simp [hh] at hi
    · rw [hom_other hne, metaSig_fixed hm (fun c' h => hom_fix hH hL h)]
      refine .const (d := d) ?_
      rw [homSig_meta (by rw [metaSig_thy hm]; exact Ne.symm hH')]
      exact hm
  defn {c A d} hc := by cases homSig_df hc

end FOView

end MMT.Hom