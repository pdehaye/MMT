import MMTlib.Core.Translation

/-!
# Foundation-independent judgments and theory morphisms

MMT is *foundation-independent*: the module system (theories, morphisms) is fixed,
while the typing and equality judgments are supplied by a *foundation* — a set of
inference rules declared in a meta-theory (`api/checking/Rules.scala`,
`api/checking/Solver.scala`).

We model:
* flat signatures `Sig` (a theory after flattening): partial maps from global names to
  constant declarations (`symbols/Constant.scala`: optional type and definiens);
* judgments `Γ ⊢ t : A` and `Γ ⊢ t ≡ u : A` (`objects/Judgements.scala`);
* a `Foundation` as an abstract rule set, subject to the two closure properties that
  MMT's design implicitly relies on: rules are schematic in the symbols of the object
  theory (stable under translation along morphisms fixing the meta-theory) and in the
  ambient context (stable under adding outer variables);
* `Derivable F S J`: derivability of `J` over signature `S` with foundation `F`;
* `IsMorphism F S T σ`: `σ` is a well-typed morphism (MMT's view-checking conditions).

The main theorem `Derivable.trans` is the **judgment-preservation theorem** for MMT
morphisms: everything derivable in the domain translates to something derivable in
the codomain. From it we obtain the category of theories and morphisms.
-/

namespace MMT

/-- Contexts; the head is the innermost variable (`var 0`). -/
abbrev Ctx := List Term

/-- Judgments of the foundation. -/
inductive Judgment where
  | typing (Γ : Ctx) (t A : Term)
  | equal  (Γ : Ctx) (t u A : Term)
deriving DecidableEq, Repr

namespace Judgment

/-- Translation of judgments along a morphism. -/
def trans (σ : Subst) : Judgment → Judgment
  | typing Γ t A  => typing (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ)
  | equal Γ t u A => equal (Γ.map (·.trans σ)) (t.trans σ) (u.trans σ) (A.trans σ)

/-- Extending the context by outer variables `Δ`. With de Bruijn indices this
does not change any term of the judgment. -/
def extend (Δ : Ctx) : Judgment → Judgment
  | typing Γ t A  => typing (Γ ++ Δ) t A
  | equal Γ t u A => equal (Γ ++ Δ) t u A

theorem trans_comp (σ τ : Subst) (J : Judgment) :
    J.trans (σ.comp τ) = (J.trans σ).trans τ := by
  cases J <;> simp [trans, Term.trans_comp, Function.comp_def]

@[simp] theorem trans_id (J : Judgment) : J.trans Subst.id = J := by
  cases J <;> simp [trans]

end Judgment

/-- Information about a constant: optional type and optional definiens. -/
structure ConstInfo where
  tp : Option Term
  df : Option Term
deriving DecidableEq, Repr

/-- A flat signature (a flattened MMT theory). -/
abbrev Sig := GName → Option ConstInfo

/-- Inclusion of signatures. -/
def Sig.Sub (S T : Sig) : Prop := ∀ c i, S c = some i → T c = some i

/-- A foundation: the inference rules of a meta-theory such as LF.
`metaSym` are the symbols the rules may mention; morphisms must fix them. -/
structure Foundation where
  metaSym : GName → Prop
  Rule    : List Judgment → Judgment → Prop
  stable_trans : ∀ (σ : Subst), σ.Closed → (∀ c, metaSym c → σ c = .const c) →
    ∀ {ps j}, Rule ps j → Rule (ps.map (Judgment.trans σ)) (j.trans σ)
  stable_extend : ∀ (Δ : Ctx) {ps j}, Rule ps j →
    Rule (ps.map (Judgment.extend Δ)) (j.extend Δ)

/-- Derivability over a signature. Besides the foundation's rules, the module
system contributes the rules for looking up constants and expanding definitions. -/
inductive Derivable (F : Foundation) (S : Sig) : Judgment → Prop where
  | const {Γ c A d} : S c = some ⟨some A, d⟩ → Derivable F S (.typing Γ (.const c) A)
  | defn  {Γ c A d} : S c = some ⟨some A, some d⟩ →
      Derivable F S (.equal Γ (.const c) d A)
  | rule  {ps j} : F.Rule ps j → (∀ p ∈ ps, Derivable F S p) → Derivable F S j

namespace Derivable

variable {F : Foundation}

/-- Outer weakening is admissible. -/
theorem extend {S : Sig} {J : Judgment} (h : Derivable F S J) (Δ : Ctx) :
    Derivable F S (J.extend Δ) := by
  induction h with
  | const hc => exact .const hc
  | defn hc => exact .defn hc
  | rule hr _ ih =>
    refine .rule (F.stable_extend Δ hr) ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq

/-- Derivability is monotone in the signature. -/
theorem mono {S T : Sig} (hST : S.Sub T) {J : Judgment} (h : Derivable F S J) :
    Derivable F T J := by
  induction h with
  | const hc => exact .const (hST _ _ hc)
  | defn hc => exact .defn (hST _ _ hc)
  | rule hr _ ih => exact .rule hr ih

end Derivable

/-- `σ` is a well-typed morphism from `S` to `T` (the conditions MMT checks for a view):
assignments are closed, meta-symbols are fixed, every typed constant is mapped to a
term of the translated type, and definitions are respected. -/
structure IsMorphism (F : Foundation) (S T : Sig) (σ : Subst) : Prop where
  closed  : σ.Closed
  fixMeta : ∀ c, F.metaSym c → σ c = .const c
  typed   : ∀ {c A d}, S c = some ⟨some A, d⟩ →
    Derivable F T (.typing [] (σ c) (A.trans σ))
  defn    : ∀ {c A d}, S c = some ⟨some A, some d⟩ →
    Derivable F T (.equal [] (σ c) (d.trans σ) (A.trans σ))

/-- **Judgment preservation** (the fundamental theorem of MMT morphisms):
a well-typed morphism `σ : S → T` maps derivable judgments over `S` to derivable
judgments over `T`. -/
theorem Derivable.trans {F : Foundation} {S T : Sig} {σ : Subst}
    (hσ : IsMorphism F S T σ) {J : Judgment} (h : Derivable F S J) :
    Derivable F T (J.trans σ) := by
  induction h with
  | @const Γ c A d hc =>
    have := (hσ.typed hc).extend (Γ.map (·.trans σ))
    simpa [Judgment.extend, Judgment.trans, Term.trans] using this
  | @defn Γ c A d hc =>
    have := (hσ.defn hc).extend (Γ.map (·.trans σ))
    simpa [Judgment.extend, Judgment.trans, Term.trans] using this
  | rule hr _ ih =>
    refine .rule (F.stable_trans σ hσ.closed hσ.fixMeta hr) ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq

/-- Special case: well-typed terms are mapped to well-typed terms. -/
theorem IsMorphism.typing {F : Foundation} {S T : Sig} {σ : Subst}
    (hσ : IsMorphism F S T σ) {Γ : Ctx} {t A : Term}
    (h : Derivable F S (.typing Γ t A)) :
    Derivable F T (.typing (Γ.map (·.trans σ)) (t.trans σ) (A.trans σ)) :=
  Derivable.trans hσ h

namespace IsMorphism

variable {F : Foundation}

/-- Identity morphisms. -/
theorem id (S : Sig) : IsMorphism F S S Subst.id where
  closed := Subst.Closed.id
  fixMeta _ _ := rfl
  typed hc := by rw [Term.trans_id]; exact Derivable.const hc
  defn hc := by rw [Term.trans_id, Term.trans_id]; exact Derivable.defn hc

/-- Inclusions of signatures are morphisms (MMT `include`). -/
theorem incl {S T : Sig} (hST : S.Sub T) : IsMorphism F S T Subst.id where
  closed := Subst.Closed.id
  fixMeta _ _ := rfl
  typed hc := by rw [Term.trans_id]; exact Derivable.const (hST _ _ hc)
  defn hc := by rw [Term.trans_id, Term.trans_id]; exact Derivable.defn (hST _ _ hc)

/-- Composition of morphisms; a consequence of judgment preservation. -/
theorem comp {S T U : Sig} {σ τ : Subst}
    (hσ : IsMorphism F S T σ) (hτ : IsMorphism F T U τ) :
    IsMorphism F S U (σ.comp τ) where
  closed := hσ.closed.comp hτ.closed
  fixMeta c hc := by simp [Subst.comp, hσ.fixMeta c hc, Term.trans, hτ.fixMeta c hc]
  typed hc := by
    have := Derivable.trans hτ (hσ.typed hc)
    simpa [Judgment.trans, Term.trans_comp, Subst.comp] using this
  defn hc := by
    have := Derivable.trans hτ (hσ.defn hc)
    simpa [Judgment.trans, Term.trans_comp, Subst.comp] using this

end IsMorphism

/-! ## The category of theories and morphisms -/

/-- Morphisms `S → T` over a foundation. -/
def Mor (F : Foundation) (S T : Sig) := { σ : Subst // IsMorphism F S T σ }

namespace Mor

variable {F : Foundation} {S T U V : Sig}

def id (S : Sig) : Mor F S S := ⟨Subst.id, IsMorphism.id S⟩

def comp (σ : Mor F S T) (τ : Mor F T U) : Mor F S U := ⟨σ.1.comp τ.1, σ.2.comp τ.2⟩

theorem ext {σ τ : Mor F S T} (h : σ.1 = τ.1) : σ = τ := Subtype.ext h

@[simp] theorem id_comp (σ : Mor F S T) : (Mor.id S).comp σ = σ := ext (Subst.id_comp _)

@[simp] theorem comp_id (σ : Mor F S T) : σ.comp (Mor.id T) = σ := ext (Subst.comp_id _)

theorem comp_assoc (σ : Mor F S T) (τ : Mor F T U) (ρ : Mor F U V) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := ext (Subst.comp_assoc _ _ _)

/-- Translation of judgments is functorial. -/
theorem trans_comp (σ : Mor F S T) (τ : Mor F T U) (J : Judgment) :
    J.trans (σ.comp τ).1 = (J.trans σ.1).trans τ.1 := Judgment.trans_comp _ _ _

end Mor

end MMT
