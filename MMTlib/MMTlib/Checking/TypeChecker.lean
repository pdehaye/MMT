import MMTlib.Foundations.LF.Basic

/-!
# A sound type checker for LF

MMT checks judgments with a rule-based algorithm (`api/checking/Solver.scala`). Its
judgments are type inference, type checking (with conversion) and equality checking.
Foundations contribute inference, typing, equality and computation rules
(`api/checking/Rules.scala`).

This file is an executable model of that algorithm for LF:
* `infer`: inference rules for variables, constants, `type`, Π, λ and application;
* `check`: inference, then a syntactic match or the conversion rule;
* `eq`: equality checking by reflexivity, δ-expansion of definitions, β-reduction,
  and congruence for application, Π and λ.

Each function returns, together with its answer, a *derivation* of the judgment it
claims, so the checker is sound by construction. `check_sound` and `eq_sound` state
this for the Boolean interface. The functions take a fuel argument, which bounds the
depth of the search, and run in the kernel (see `Example.lean`).

Unknowns (implicit arguments, their solutions and type reconstruction) are treated in
`Unknowns.lean`. The checker is complete for syntax-directed typing
(`CheckerComplete.lean`); beyond that, `false` only means that no derivation was found.
-/

namespace MMT.LF.Checker

open Term Judgment

variable (S : Sig)

/-- Derivability over `S` in LF. -/
abbrev D (J : Judgment) : Prop := Derivable foundation S J

variable {S}

theorem r0 {j} (h : Rule [] j) : D S j := .rule h (by simp)
theorem r1 {p j} (h : Rule [p] j) (hp : D S p) : D S j := .rule h (by simpa using hp)
theorem r2 {p q j} (h : Rule [p, q] j) (hp : D S p) (hq : D S q) : D S j :=
  .rule h (by simp; exact ⟨hp, hq⟩)

variable (S)

mutual

/-- Type inference: returns a type together with a typing derivation. -/
def infer : Nat → (Γ : Ctx) → (t : Term) → Option {A : Term // D S (.typing Γ t A)}
  | 0, _, _ => none
  | n + 1, Γ, .var i =>
    match h : Γ[i]? with
    | some A => some ⟨A.liftN (i + 1) 0, r0 (Rule.var Γ i A h)⟩
    | none => none
  | _ + 1, Γ, .const c =>
    if hc : c = typeN then some ⟨kind, by subst hc; exact r0 (Rule.univ Γ)⟩
    else
      match h : S c with
      | some ⟨some A, _⟩ => some ⟨A, .const h⟩
      | _ => none
  | n + 1, Γ, .bind (.const b) A body =>
    if hb : b = piN then
      match check n Γ A type, infer n (A :: Γ) body with
      | some hA, some ⟨U, hU⟩ =>
        if h1 : U = type then
          some ⟨type, by subst hb h1; exact r2 (Rule.piType Γ A body) hA.down hU⟩
        else if h2 : U = kind then
          some ⟨kind, by subst hb h2; exact r2 (Rule.piKind Γ A body) hA.down hU⟩
        else none
      | _, _ => none
    else if hl : b = lamN then
      match check n Γ A type, infer n (A :: Γ) body with
      | some hA, some ⟨B, hB⟩ =>
        some ⟨Pi A B, by subst hl; exact r2 (Rule.lamI Γ A B body) hA.down hB⟩
      | _, _ => none
    else none
  | n + 1, Γ, .app f a =>
    match infer n Γ f with
    | some ⟨.bind (.const p) A B, hf⟩ =>
      if hp : p = piN then
        match check n Γ a A with
        | some ha => some ⟨inst 0 a B, by subst hp; exact r2 (Rule.appE Γ A B f a) hf ha.down⟩
        | none => none
      else none
    | _ => none
  | _ + 1, _, _ => none

/-- Type checking: inference followed by syntactic match or conversion. -/
def check : Nat → (Γ : Ctx) → (t A : Term) → Option (PLift (D S (.typing Γ t A)))
  | 0, _, _, _ => none
  | n + 1, Γ, t, A =>
    match infer n Γ t with
    | some ⟨A', h⟩ =>
      if hA : A' = A then some ⟨hA ▸ h⟩
      else
        match infer n Γ A with
        | some ⟨U, _⟩ =>
          match eq n Γ A' A U with
          | some he => some ⟨r2 (Rule.conv Γ t A' A U) h he.down⟩
          | none => none
        | none => none
    | none => none

/-- Equality checking at a given type. -/
def eq : Nat → (Γ : Ctx) → (t u A : Term) → Option (PLift (D S (.equal Γ t u A)))
  | 0, _, _, _, _ => none
  | n + 1, Γ, t, u, A =>
    (if htu : t = u then
      match check n Γ t A with
      | some h => some ⟨htu ▸ r1 (Rule.refl Γ t A) h.down⟩
      | none => none
     else none) <|>
    -- δ-expansion on the left
    (match t with
     | .const c =>
       match hc : S c with
       | some ⟨some Ac, some d⟩ =>
         if hA : Ac = A then
           match eq n Γ d u A with
           | some h => some ⟨r2 (Rule.trans Γ (.const c) d u A) (hA ▸ .defn hc) h.down⟩
           | none => none
         else none
       | _ => none
     | _ => none) <|>
    -- δ-expansion on the right
    (match u with
     | .const c =>
       match hc : S c with
       | some ⟨some Ac, some d⟩ =>
         if hA : Ac = A then
           match eq n Γ t d A with
           | some h => some ⟨r2 (Rule.trans Γ t d (.const c) A) h.down
               (r1 (Rule.symm Γ (.const c) d A) (hA ▸ .defn hc))⟩
           | none => none
         else none
       | _ => none
     | _ => none) <|>
    -- β-reduction on the left
    (match t with
     | .app (.bind (.const l) A' b) a =>
       if hl : l = lamN then
         match infer n (A' :: Γ) b, check n Γ a A' with
         | some ⟨B, hB⟩, some ha =>
           if hBA : inst 0 a B = A then
             match eq n Γ (inst 0 a b) u A with
             | some h => some ⟨r2 (Rule.trans Γ _ (inst 0 a b) u A)
                 (by subst hl hBA; exact r2 (Rule.beta Γ A' B b a) hB ha.down) h.down⟩
             | none => none
           else none
         | _, _ => none
       else none
     | _ => none) <|>
    -- β-reduction on the right
    (match u with
     | .app (.bind (.const l) A' b) a =>
       if hl : l = lamN then
         match infer n (A' :: Γ) b, check n Γ a A' with
         | some ⟨B, hB⟩, some ha =>
           if hBA : inst 0 a B = A then
             match eq n Γ t (inst 0 a b) A with
             | some h => some ⟨r2 (Rule.trans Γ t (inst 0 a b) _ A) h.down
                 (r1 (Rule.symm Γ _ (inst 0 a b) A)
                   (by subst hl hBA; exact r2 (Rule.beta Γ A' B b a) hB ha.down))⟩
             | none => none
           else none
         | _, _ => none
       else none
     | _ => none) <|>
    -- congruences
    (match t, u with
     | .app f a, .app f' a' =>
       match infer n Γ f with
       | some ⟨.bind (.const p) A₁ B₁, _⟩ =>
         if hp : p = piN then
           if hB : inst 0 a B₁ = A then
             match eq n Γ f f' (.bind (.const p) A₁ B₁), eq n Γ a a' A₁ with
             | some hf, some ha => some ⟨by
                 subst hp hB; exact r2 (Rule.appCong Γ A₁ B₁ f f' a a') hf.down ha.down⟩
             | _, _ => none
           else none
         else none
       | _ => none
     | .bind (.const p) A₁ B₁, .bind (.const p') A₂ B₂ =>
       if hp : p = piN ∧ p' = piN then
         match eq n Γ A₁ A₂ type, eq n (A₁ :: Γ) B₁ B₂ (A.liftN 1 0) with
         | some hA, some hB => some ⟨by
             obtain ⟨rfl, rfl⟩ := hp; exact r2 (Rule.piCong Γ A₁ A₂ B₁ B₂ A) hA.down hB.down⟩
         | _, _ => none
       else if hl : p = lamN ∧ p' = lamN then
         match A with
         | .bind (.const q) A₃ B =>
           if hq : q = piN ∧ A₃ = A₁ then
             match eq n Γ A₁ A₂ type, eq n (A₁ :: Γ) B₁ B₂ B with
             | some hA, some hb => some ⟨by
                 obtain ⟨rfl, rfl⟩ := hl; obtain ⟨rfl, rfl⟩ := hq
                 exact r2 (Rule.lamCong Γ A₃ A₂ B B₁ B₂) hA.down hb.down⟩
             | _, _ => none
           else none
         | _ => none
       else none
     | _, _ => none)

end

/-- Default search depth. -/
def fuel : Nat := 64

/-- Boolean interface: does `t` check against `A` in context `Γ`? -/
def typeCheck (Γ : Ctx) (t A : Term) : Bool := (check S fuel Γ t A).isSome

/-- Boolean interface: are `t` and `u` equal at type `A`? -/
def eqCheck (Γ : Ctx) (t u A : Term) : Bool := (eq S fuel Γ t u A).isSome

variable {S}

/-- **Soundness of type checking.** -/
theorem check_sound {Γ : Ctx} {t A : Term} (h : typeCheck S Γ t A = true) :
    D S (.typing Γ t A) := by
  unfold typeCheck at h
  cases hc : check S fuel Γ t A with
  | none => rw [hc] at h; cases h
  | some p => exact p.down

/-- **Soundness of equality checking.** -/
theorem eq_sound {Γ : Ctx} {t u A : Term} (h : eqCheck S Γ t u A = true) :
    D S (.equal Γ t u A) := by
  unfold eqCheck at h
  cases hc : eq S fuel Γ t u A with
  | none => rw [hc] at h; cases h
  | some p => exact p.down

/-- **Soundness of type inference**, at any fuel. -/
theorem infer_sound {n : Nat} {Γ : Ctx} {t A : Term} {h}
    (_ : infer S n Γ t = some ⟨A, h⟩) : D S (.typing Γ t A) := h

end MMT.LF.Checker
