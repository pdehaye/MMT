import MMTFormal.Modules
import MMTFormal.Pushout

/-!
# Flattening a structure is a pushout

Let `H` declare `structure s : Sdom = as`. This file proves that `flat L H` is,
literally, the pushout signature of `Pushout.lean` for the following data:

* the extension `S'` is the flattening of the domain, `flat L Sdom`;
* the shared part `S` consists of the constants of `S'` that are already visible in `H`;
* the base `T` is the host without the copies induced by `s`;
* the morphism `S → T` is the identity, since shared constants are not renamed;
* the renaming `c ↦ H?s/c` is built from complex names (`LName.sub`);
* the assignments are those of the structure.

The pushout morphism `σ'` also coincides with the module-level `structMor` on the
constants of `Sdom`. Consequently, the universal property of the pushout holds for
the host theory and its structure morphism (`flat_struct_universal`).

The only hypothesis besides the declaration of the structure is that `flat L Sdom` is
closed, i.e. declarations of `Sdom` only refer to constants visible in `Sdom`.
-/

namespace MMT

/-- The renaming of a structure `s` in `H`: `c ↦ H?s/c`, with its partial inverse. -/
def structRenaming (H : ThyName) (s : String) : Renaming where
  fwd c := ⟨H, .sub s c.thy c.name⟩
  bwd d := match d.name with
    | .sub s' S0 o => if d.thy = H ∧ s' = s then some ⟨S0, o⟩ else none
    | .base _ => none
  bwd_fwd c := by simp
  fwd_bwd c d h := by
    obtain ⟨H', n⟩ := d
    cases n with
    | base => simp at h
    | sub s' S0 o =>
      simp only at h
      split at h
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; cases h; rfl
      · cases h

open Classical in
/-- The shared part: constants of the domain that are already visible in the host. -/
noncomputable def sharedSig (L : Library) (H Sdom : ThyName) : Sig := fun c =>
  if Visible L H c.thy then flat L Sdom c else none

/-- The host without the copies induced by `s`. -/
noncomputable def hostBase (L : Library) (H : ThyName) (s : String) : Sig := fun d =>
  if ((structRenaming H s).bwd d).isSome then none else flat L H d

theorem flat_self {L : Library} {H : ThyName} {n : LName} :
    flat L H ⟨H, n⟩ = homeInfo L H n := by
  simp [flat, Visible.refl]

section

variable {L : Library} {H Sdom : ThyName} {s : String} {as : List (GName × Term)}

/-- On the constants of the domain, the pushout morphism is the structure morphism. -/
theorem poMor_eq_structMor {c : GName} (hc : (flat L Sdom).Has c) :
    poMor (sharedSig L H Sdom) (flat L Sdom) Subst.id (structRenaming H s) c =
      structMor L H s c := by
  simp only [Sig.Has] at hc
  by_cases hv : Visible L H c.thy
  · have : isNew (sharedSig L H Sdom) (flat L Sdom) c = false := by
      simp [isNew, sharedSig, hv, hc]
    simp [poMor, this, structMor_shared hv, Subst.id]
  · have : isNew (sharedSig L H Sdom) (flat L Sdom) c = true := by
      simp [isNew, sharedSig, hv, hc]
    simp [poMor, this, structMor_copy hv, structRenaming]

/-- **Flattening a structure is a pushout.** -/
theorem flat_struct_eq_pushout
    (hs : (L H).bind (·.structLookup s) = some (Sdom, as)) (hcl : (flat L Sdom).Closed) :
    flat L H = poSig (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) Subst.id
      (structRenaming H s) (fun c => as.lookup c) := by
  funext d
  obtain ⟨H', n⟩ := d
  -- the case of a constant that is not a copy induced by `s`
  have other : (structRenaming H s).bwd ⟨H', n⟩ = none →
      flat L H ⟨H', n⟩ = poSig (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) Subst.id
        (structRenaming H s) (fun c => as.lookup c) ⟨H', n⟩ := by
    intro hb
    cases h : flat L H ⟨H', n⟩ <;> simp [poSig, hostBase, hb, h]
  cases n with
  | base n => exact other (by simp [structRenaming])
  | sub s' S0 o =>
    by_cases hH : H' = H ∧ s' = s
    case neg => exact other (by simp [structRenaming, hH])
    rw [hH.1, hH.2]
    have hb : (structRenaming H s).bwd ⟨H, .sub s S0 o⟩ = some ⟨S0, o⟩ := by
      simp [structRenaming]
    have hT : hostBase L H s ⟨H, .sub s S0 o⟩ = none := by simp [hostBase, hb]
    -- the right-hand side, unfolded
    have rhs : poSig (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) Subst.id
        (structRenaming H s) (fun c => as.lookup c) ⟨H, .sub s S0 o⟩ =
        if isNew (sharedSig L H Sdom) (flat L Sdom) ⟨S0, o⟩ then
          (flat L Sdom ⟨S0, o⟩).map (poInfo (sharedSig L H Sdom) (flat L Sdom) Subst.id
            (structRenaming H s) (fun c => as.lookup c) ⟨S0, o⟩)
        else none := by
      simp only [poSig, hT, hb]
    rw [rhs, flat_self]
    by_cases hv : Visible L Sdom S0
    · by_cases hnv : Visible L H S0
      · -- shared: no copy on either side
        have hn : isNew (sharedSig L H Sdom) (flat L Sdom) ⟨S0, o⟩ = false := by
          simp [isNew, sharedSig, hnv]
        have hc : ¬ (Visible L Sdom S0 ∧ ¬ Visible L H S0) := fun h => h.2 hnv
        simp [homeInfo, hs, hc, hn]
      · cases hi : homeInfo L S0 o with
        | none =>
          have hc : Visible L Sdom S0 ∧ ¬ Visible L H S0 := ⟨hv, hnv⟩
          have hf : flat L Sdom ⟨S0, o⟩ = none := by simp [flat, hv, hi]
          simp [homeInfo, hs, hc, hi, hf]
        | some i =>
          have hf : flat L Sdom ⟨S0, o⟩ = some i := by simp [flat, hv, hi]
          have hn : isNew (sharedSig L H Sdom) (flat L Sdom) ⟨S0, o⟩ = true := by
            simp [isNew, sharedSig, hnv, hf]
          rw [homeInfo_copy hs hv hnv hi, hn, hf]
          -- the translations agree since the declaration only uses constants of `Sdom`
          have agree : ∀ x : Term, x.UsesOnly (flat L Sdom).Has →
              x.trans (structMor L H s) =
                x.trans (poMor (sharedSig L H Sdom) (flat L Sdom) Subst.id
                  (structRenaming H s)) :=
            fun x hx => Term.trans_congr hx (fun c hc => (poMor_eq_structMor hc).symm)
          obtain ⟨htp, hdf⟩ := hcl _ i hf
          obtain ⟨tp, df⟩ := i
          simp only [Option.map_some, poInfo, ↓reduceIte]
          congr 2
          · cases tp with
            | none => rfl
            | some A => simp [agree A (htp A rfl)]
          · cases df with
            | none => rfl
            | some e => simp [agree e (hdf e rfl)]
    · have hn : isNew (sharedSig L H Sdom) (flat L Sdom) ⟨S0, o⟩ = false := by
        simp [isNew, flat, hv]
      have hc : ¬ (Visible L Sdom S0 ∧ ¬ Visible L H S0) := fun h => hv h.1
      simp [homeInfo, hs, hc, hn]

/-- **Universal property of structures.** The host theory, together with the structure
morphism and the inclusion of the rest of the host, is a pushout. Every compatible
cocone factors uniquely through `flat L H`. -/
theorem flat_struct_universal {F : Foundation} {U : Sig} {τ μ : Subst}
    (hs : (L H).bind (·.structLookup s) = some (Sdom, as)) (hcl : (flat L Sdom).Closed)
    (hp : PushoutHyp F (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) Subst.id
      (structRenaming H s) (fun c => as.lookup c))
    (hland : Subst.id.LandsIn (sharedSig L H Sdom) (hostBase L H s))
    (hT : (hostBase L H s).Closed)
    (hτ : IsMorphism F (hostBase L H s) U τ) (hμ : IsMorphism F (flat L Sdom) U μ)
    (hcomm : ∀ c, (sharedSig L H Sdom).Has c → μ c = τ c)
    (hassign : ∀ c t A, as.lookup c = some t → flat L Sdom c = some ⟨some A, none⟩ →
      Derivable F U (.equal [] (μ c)
        (t.trans (poMed (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) τ μ
          (structRenaming H s))) (A.trans μ))) :
    let med := poMed (sharedSig L H Sdom) (flat L Sdom) (hostBase L H s) τ μ (structRenaming H s)
    IsMorphism F (flat L H) U med ∧
    (∀ d, (hostBase L H s).Has d → med d = τ d) ∧
    (∀ c, (flat L Sdom).Has c → (structMor L H s c).trans med = μ c) ∧
    (∀ u : Subst, (∀ d, (hostBase L H s).Has d → u d = τ d) →
      (∀ c, (flat L Sdom).Has c → (structMor L H s c).trans u = μ c) →
      ∀ d, (flat L H).Has d → u d = med d) := by
  intro med
  obtain ⟨h1, h2, h3, h4⟩ := pushout_universal hp hland hT hcl hτ hμ
    (fun c hc => by rw [hcomm c hc]; rfl) hassign
  rw [← flat_struct_eq_pushout hs hcl] at h1 h4
  refine ⟨h1, h2, fun c hc => ?_, fun u hu1 hu2 => h4 u hu1 (fun c hc => ?_)⟩
  · rw [← poMor_eq_structMor hc]; exact h3 c hc
  · rw [poMor_eq_structMor hc]; exact hu2 c hc

end

end MMT
