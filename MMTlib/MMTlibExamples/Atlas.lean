import MMTlib.Foundations.LF.Basic
import MMTlib.Modules.Basic
import MMTlib.Modules.PartialView
import MMTlib.Checking.ModuleChecker

/-!
# An atlas of a research programme as an MMT theory graph

The programme relates several bodies of mathematics: Dehaye's combinatorial form of the
CFKRS moment recipe (arXiv:1201.4478, Theorem 3), its U(N) and ζ instances, the claimed RH
formalisation `pdehaye/riemann-hypothesis-lean` (Fock norms, hook products, the basis of the
dual Weyl module), the Lean library `pdehaye/RMTlib` (growth-diagram RSK, bridges), and an
analogy with Hawking radiation in null coordinates. Moving between them is exactly what views
are for, so this file records the programme as a theory graph and lets the verified checkers
of `MMTlib.Checking.ModuleChecker` certify the links.

## The pattern: spans, as in analogue gravity

Analogue gravity relates a model (sound in a moving fluid) and a target (a black hole) through
a shared *kinematic* theory (null coordinates, a horizon), not through a direct dictionary.
Here the same shape appears three times:

```
            Recipe                    NullLattice                 HookFact
           /      \                  /           \                    \
       UNModel   ZetaModel      GrowthRSK      Kruskal               RHFock
```

* The legs of each span are **total views, checked by `checkView` and `decide`**.
* The direct link between the two models is a **partial view**: `checkView` rejects it as a
  total view, and `unassigned` lists exactly the constants with no counterpart. Those lists are
  the formal content of "what does not transfer": ζ's arithmetic factor and its cutoff-free
  prime sum have no U(N) counterpart; the exponential map of Kruskal coordinates has no
  counterpart in growth diagrams.

The theories are vocabulary-level LF signatures (propositions as types: `ded : prop → type`).
They do not contain the mathematics, which lives in Lean libraries and scripts; the table
`edges` at the end records, for every link, its status (proved / checked / sorried /
analogy / rejected) and the file that justifies it.
-/

namespace MMT.Atlas

open LF

/-- A constant of theory `T`. -/
def k (T n : String) : Term := .const ⟨T, n⟩

/-- `f a`, `f a b`. -/
def ap (f a : Term) : Term := .app f a
def ap2 (f a b : Term) : Term := .app (.app f a) b

/-- The LF meta-theory. -/
def lfThy : Theory :=
  { metaThy := none,
    decls := [.const "type" none none, .const "kind" none none,
              .const "Pi" none none, .const "lambda" none none] }

/-! ## Span 1: the moment recipe and its instances -/

/-- The declarations of Theorem 3 (Dehaye), over a theory named `T`: shapes, coefficients,
local data, skew dimensions `dim`, the complement `S_k` (`comp`), the arithmetic weights
`d_κλ` (`weight`), and the formula `c_M = 1/(k²−M)! Σ d_κλ dim(λ, S_k(κ))` (`thm3`). -/
def recipeDecls (T : String) : List Decl :=
  [.const "Shape" (some type) none,
   .const "Num" (some type) none,
   .const "Local" (some type) none,
   .const "prop" (some type) none,
   .const "ded" (some (arrow (k T "prop") type)) none,
   .const "dim" (some (arrow (k T "Shape") (arrow (k T "Shape") (k T "Num")))) none,
   .const "comp" (some (arrow (k T "Shape") (k T "Shape"))) none,
   .const "weight" (some (arrow (k T "Local") (arrow (k T "Shape") (arrow (k T "Shape") (k T "Num"))))) none,
   .const "formula" (some (arrow (k T "Local") (k T "prop"))) none,
   .const "thm3" (some (Pi (k T "Local") (ap (k T "ded") (ap (k T "formula") (.var 0))))) none]

/-- The interface: Theorem 3 with the local data abstract. -/
def recipe : Theory := { metaThy := some "LF", decls := recipeDecls "Recipe" }

/-- U(N): one place, kernel `1/(1−e^{−u})` (Bernoulli numbers), conductor `N`. -/
def unModel : Theory :=
  { metaThy := some "LF",
    decls := recipeDecls "UNModel" ++
      [.const "bernoulli" (some (k "UNModel" "Local")) none,
       .const "conductorN" (some (k "UNModel" "Num")) none] }

/-- ζ: the product over primes, conductor `log(t/2π)`, the arithmetic factor `a_k`, and the
cutoff-free evaluation of `Σ_p log A_p` (analytic continuation in the scaling of `1/p`). -/
def zetaModel : Theory :=
  { metaThy := some "LF",
    decls := recipeDecls "ZetaModel" ++
      [.const "primes" (some (k "ZetaModel" "Local")) none,
       .const "conductorLogT" (some (k "ZetaModel" "Num")) none,
       .const "arithFactor" (some (k "ZetaModel" "Num")) none,
       .const "cutoffFree" (some (k "ZetaModel" "prop")) none,
       .const "cutoffFreeThm" (some (ap (k "ZetaModel" "ded") (k "ZetaModel" "cutoffFree"))) none] }

/-- The assignments of the recipe vocabulary of `S` to that of `T` (same local names). -/
def recipeAssign (T : String) : List (LName × Term) :=
  ["Shape", "Num", "Local", "prop", "ded", "dim", "comp", "weight", "formula", "thm3"].map
    fun n => (.base n, k T n)

/-- `Recipe → UNModel`: Theorem 3 holds for U(N) (checked: `scripts/un_test.py`, k ≤ 3). -/
def recipeToUN : View := { dom := "Recipe", cod := "UNModel", assign := recipeAssign "UNModel" }

/-- `Recipe → ZetaModel`: Theorem 3 for ζ (the paper; numerics in `scripts/places.py`). -/
def recipeToZeta : View := { dom := "Recipe", cod := "ZetaModel", assign := recipeAssign "ZetaModel" }

/-- The direct analogy `ZetaModel ⇢ UNModel`: primes ↦ the single place, `log(t/2π) ↦ N`.
The arithmetic factor and the cutoff-free prime sum are left unassigned. -/
def zetaToUN : View :=
  { dom := "ZetaModel", cod := "UNModel",
    assign := recipeAssign "UNModel" ++
      [(.base "primes", k "UNModel" "bernoulli"), (.base "conductorLogT", k "UNModel" "conductorN")] }

/-! ## Span 2: null lattices -/

/-- A characteristic (Goursat) problem on a null lattice: a value at each corner of a unit
diamond is computed from the past corner, the two side corners and a source. -/
def nullLattice : Theory :=
  { metaThy := some "LF",
    decls := [.const "Val" (some type) none,
              .const "Src" (some type) none,
              .const "rule" (some (arrow (k "NullLattice" "Val") (arrow (k "NullLattice" "Val")
                (arrow (k "NullLattice" "Val") (arrow (k "NullLattice" "Src") (k "NullLattice" "Val")))))) none] }

/-- Fomin's growth diagrams (`RMT.Growth.localRule`): shapes on a grid, the permutation as source. -/
def growthRSK : Theory :=
  { metaThy := some "LF",
    decls := [.const "Shape" (some type) none,
              .const "Bit" (some type) none,
              .const "localRule" (some (arrow (k "GrowthRSK" "Shape") (arrow (k "GrowthRSK" "Shape")
                (arrow (k "GrowthRSK" "Shape") (arrow (k "GrowthRSK" "Bit") (k "GrowthRSK" "Shape")))))) none,
              .const "Tableau" (some type) none,
              .const "Perm" (some type) none,
              .const "rsk" (some (arrow (k "GrowthRSK" "Perm") (k "GrowthRSK" "Tableau"))) none] }

/-- A massless field in Kruskal null coordinates: the discretized wave equation is a null-lattice
rule; the exponential map `U = −e^{−κu}` to asymptotic coordinates produces the redshift. -/
def kruskal : Theory :=
  { metaThy := some "LF",
    decls := [.const "Field" (some type) none,
              .const "Source" (some type) none,
              .const "waveRule" (some (arrow (k "Kruskal" "Field") (arrow (k "Kruskal" "Field")
                (arrow (k "Kruskal" "Field") (arrow (k "Kruskal" "Source") (k "Kruskal" "Field")))))) none,
              .const "Coord" (some type) none,
              .const "kappa" (some type) none,
              .const "kruskalMap" (some (arrow (k "Kruskal" "kappa") (arrow (k "Kruskal" "Coord") (k "Kruskal" "Coord")))) none] }

/-- Growth diagrams are a null-lattice scheme (by definition of `RMT.Growth.row`). -/
def nullToGrowth : View :=
  { dom := "NullLattice", cod := "GrowthRSK",
    assign := [(.base "Val", k "GrowthRSK" "Shape"), (.base "Src", k "GrowthRSK" "Bit"),
               (.base "rule", k "GrowthRSK" "localRule")] }

/-- The discretized wave equation in null coordinates is a null-lattice scheme. -/
def nullToKruskal : View :=
  { dom := "NullLattice", cod := "Kruskal",
    assign := [(.base "Val", k "Kruskal" "Field"), (.base "Src", k "Kruskal" "Source"),
               (.base "rule", k "Kruskal" "waveRule")] }

/-- The direct analogy `Kruskal ⇢ GrowthRSK`: the local rule transfers; the exponential map
and the surface gravity do not (the VKLS edge is a square-root soft edge, not a linear horizon). -/
def kruskalToGrowth : View :=
  { dom := "Kruskal", cod := "GrowthRSK",
    assign := [(.base "Field", k "GrowthRSK" "Shape"), (.base "Source", k "GrowthRSK" "Bit"),
               (.base "waveRule", k "GrowthRSK" "localRule")] }

/-! ## Span 3: hook products and Fock norms -/

/-- `N(λ) = H(λ)`: a norm equals the hook product of the shape. -/
def hookFact : Theory :=
  { metaThy := some "LF",
    decls := [.const "Shape" (some type) none, .const "Num" (some type) none,
              .const "prop" (some type) none,
              .const "ded" (some (arrow (k "HookFact" "prop") type)) none,
              .const "eq" (some (arrow (k "HookFact" "Num") (arrow (k "HookFact" "Num") (k "HookFact" "prop")))) none,
              .const "N" (some (arrow (k "HookFact" "Shape") (k "HookFact" "Num"))) none,
              .const "H" (some (arrow (k "HookFact" "Shape") (k "HookFact" "Num"))) none,
              .const "fact" (some (Pi (k "HookFact" "Shape")
                (ap (k "HookFact" "ded") (ap2 (k "HookFact" "eq") (ap (k "HookFact" "N") (.var 0)) (ap (k "HookFact" "H") (.var 0)))))) none] }

/-- The RH formalisation: `fockQ (hw ν) (hw ν) · ∏ (ν_i − ν_j + j − i) = ∏ (ν_i + N − 1 − i)!`
(`PI.HookSteps.HookNorm`, proved), i.e. the Fock norm² of the highest-weight vector is the
hook product. -/
def rhFock : Theory :=
  { metaThy := some "LF",
    decls := [.const "Weight" (some type) none, .const "Rat" (some type) none,
              .const "prop" (some type) none,
              .const "ded" (some (arrow (k "RHFock" "prop") type)) none,
              .const "eq" (some (arrow (k "RHFock" "Rat") (arrow (k "RHFock" "Rat") (k "RHFock" "prop")))) none,
              .const "fockNormHw" (some (arrow (k "RHFock" "Weight") (k "RHFock" "Rat"))) none,
              .const "hookProd" (some (arrow (k "RHFock" "Weight") (k "RHFock" "Rat"))) none,
              .const "hookNorm" (some (Pi (k "RHFock" "Weight")
                (ap (k "RHFock" "ded") (ap2 (k "RHFock" "eq") (ap (k "RHFock" "fockNormHw") (.var 0)) (ap (k "RHFock" "hookProd") (.var 0)))))) none] }

/-- `HookFact → RHFock`: the norm is the Fock norm of the highest-weight vector. -/
def hookToRH : View :=
  { dom := "HookFact", cod := "RHFock",
    assign := [(.base "Shape", k "RHFock" "Weight"), (.base "Num", k "RHFock" "Rat"),
               (.base "prop", k "RHFock" "prop"), (.base "ded", k "RHFock" "ded"),
               (.base "eq", k "RHFock" "eq"), (.base "N", k "RHFock" "fockNormHw"),
               (.base "H", k "RHFock" "hookProd"), (.base "fact", k "RHFock" "hookNorm")] }

/-! ## Modular part: a shared logic, statements, implementations, connectors

The theories below include a common `Logic`, which every view keeps fixed (MMT's shared
includes). Each mathematical claim has a *statement theory* with views into the theories where it
is established; a link between two developments is a *connector theory* that includes both and
declares the bridging lemma. -/

/-- Propositions as types, shared by all modular theories. -/
def logic : Theory :=
  { metaThy := some "LF",
    decls := [.const "prop" (some type) none,
              .const "ded" (some (arrow (k "Logic" "prop") type)) none,
              .const "iff" (some (arrow (k "Logic" "prop") (arrow (k "Logic" "prop") (k "Logic" "prop")))) none,
              .const "and" (some (arrow (k "Logic" "prop") (arrow (k "Logic" "prop") (k "Logic" "prop")))) none] }

/-- `ded (iff p q)` over the shared logic. -/
def dedIff (p q : Term) : Term := ap (k "Logic" "ded") (ap2 (k "Logic" "iff") p q)

/-- Statement: **Lemma 6** of Dehaye (complementary in the square ⟺ shifted sequences
partition `{0, …, 2k−1}`), with Macdonald's identity (I.1.7) as its input. -/
def complementarity : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Shape" (some type) none,
              .const "complementary" (some (arrow (k "Complementarity" "Shape") (arrow (k "Complementarity" "Shape") (k "Logic" "prop")))) none,
              .const "shiftedPartition" (some (arrow (k "Complementarity" "Shape") (arrow (k "Complementarity" "Shape") (k "Logic" "prop")))) none,
              .const "rowsAndColumnsPartition" (some (arrow (k "Complementarity" "Shape") (k "Logic" "prop"))) none,
              .const "macdonald" (some (Pi (k "Complementarity" "Shape")
                (ap (k "Logic" "ded") (ap (k "Complementarity" "rowsAndColumnsPartition") (.var 0))))) none,
              .const "lemma6" (some (Pi (k "Complementarity" "Shape") (Pi (k "Complementarity" "Shape")
                (dedIff (ap2 (k "Complementarity" "complementary") (.var 1) (.var 0))
                        (ap2 (k "Complementarity" "shiftedPartition") (.var 1) (.var 0)))))) none] }

/-- Implementation: `RMTlib.Tableaux.Complement` (`RMT.Complementary`, `RMT.ShiftedPartition`,
`RMT.macdonald_1_7`, `RMT.lemma6`; proved, standard axioms). -/
def rmtComplement : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "BoxPartition" (some type) none,
              .const "Complementary" (some (arrow (k "RMTlibComplement" "BoxPartition") (arrow (k "RMTlibComplement" "BoxPartition") (k "Logic" "prop")))) none,
              .const "ShiftedPartition" (some (arrow (k "RMTlibComplement" "BoxPartition") (arrow (k "RMTlibComplement" "BoxPartition") (k "Logic" "prop")))) none,
              .const "Macdonald17" (some (arrow (k "RMTlibComplement" "BoxPartition") (k "Logic" "prop"))) none,
              .const "macdonald_1_7" (some (Pi (k "RMTlibComplement" "BoxPartition")
                (ap (k "Logic" "ded") (ap (k "RMTlibComplement" "Macdonald17") (.var 0))))) none,
              .const "lemma6" (some (Pi (k "RMTlibComplement" "BoxPartition") (Pi (k "RMTlibComplement" "BoxPartition")
                (dedIff (ap2 (k "RMTlibComplement" "Complementary") (.var 1) (.var 0))
                        (ap2 (k "RMTlibComplement" "ShiftedPartition") (.var 1) (.var 0)))))) none] }

/-- `Complementarity → RMTlibComplement`: the claim is proved in RMTlib. -/
def complementarityToRMT : View :=
  { dom := "Complementarity", cod := "RMTlibComplement",
    assign := [(.base "Shape", k "RMTlibComplement" "BoxPartition"),
               (.base "complementary", k "RMTlibComplement" "Complementary"),
               (.base "shiftedPartition", k "RMTlibComplement" "ShiftedPartition"),
               (.base "rowsAndColumnsPartition", k "RMTlibComplement" "Macdonald17"),
               (.base "macdonald", k "RMTlibComplement" "macdonald_1_7"),
               (.base "lemma6", k "RMTlibComplement" "lemma6")] }

/-- Statement: the index set of a basis of `∇(ν)`, and the reading-word characterization by RSK. -/
def weylIndex : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Mat" (some type) none,
              .const "interlaced" (some (arrow (k "WeylIndex" "Mat") (k "Logic" "prop"))) none,
              .const "recordingFixed" (some (arrow (k "WeylIndex" "Mat") (k "Logic" "prop"))) none,
              .const "readingWord" (some (Pi (k "WeylIndex" "Mat")
                (dedIff (ap (k "WeylIndex" "interlaced") (.var 0)) (ap (k "WeylIndex" "recordingFixed") (.var 0))))) none] }

/-- Implementation side 1: `RMTlib.Tableaux.Interlaced` and `RMTlibTargets.readingWord`
(checked on small cases; `sorry` in general). -/
def rmtWeyl : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "FunMat" (some type) none,
              .const "Interlaced" (some (arrow (k "RMTlibWeyl" "FunMat") (k "Logic" "prop"))) none,
              .const "RecordingIsQnu" (some (arrow (k "RMTlibWeyl" "FunMat") (k "Logic" "prop"))) none,
              .const "readingWord" (some (Pi (k "RMTlibWeyl" "FunMat")
                (dedIff (ap (k "RMTlibWeyl" "Interlaced") (.var 0)) (ap (k "RMTlibWeyl" "RecordingIsQnu") (.var 0))))) none] }

/-- Implementation side 2: the RH formalisation, `Formalism.GradedWeylDivisibility`
(`Interlaced`, `ssIdx`, `SSBasis`; on `Finsupp`s). -/
def rhWeyl : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "FinsuppMat" (some type) none,
              .const "Interlaced" (some (arrow (k "RHWeylBasis" "FinsuppMat") (k "Logic" "prop"))) none,
              .const "leadingMonomialOfBasis" (some (arrow (k "RHWeylBasis" "FinsuppMat") (k "Logic" "prop"))) none,
              .const "sSBasis" (some (Pi (k "RHWeylBasis" "FinsuppMat")
                (dedIff (ap (k "RHWeylBasis" "Interlaced") (.var 0)) (ap (k "RHWeylBasis" "leadingMonomialOfBasis") (.var 0))))) none] }

/-- Connector: `bridge/RMTlibBridge/WeylBasis.lean`. It includes both sides, coerces
`Finsupp`s to functions, and states `RMT.Bridge.interlaced_iff` (proved). -/
def weylBridge : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic", .incl "RMTlibWeyl", .incl "RHWeylBasis",
              .const "coe" (some (arrow (k "RHWeylBasis" "FinsuppMat") (k "RMTlibWeyl" "FunMat"))) none,
              .const "interlaced_iff" (some (Pi (k "RHWeylBasis" "FinsuppMat")
                (dedIff (ap (k "RHWeylBasis" "Interlaced") (.var 0))
                        (ap (k "RMTlibWeyl" "Interlaced") (ap (k "WeylBridge" "coe") (.var 0)))))) none] }

/-- `WeylIndex → RMTlibWeyl`: the statement is RMTlib's `ReadingWord` (sorried target). -/
def weylIndexToRMT : View :=
  { dom := "WeylIndex", cod := "RMTlibWeyl",
    assign := [(.base "Mat", k "RMTlibWeyl" "FunMat"), (.base "interlaced", k "RMTlibWeyl" "Interlaced"),
               (.base "recordingFixed", k "RMTlibWeyl" "RecordingIsQnu"),
               (.base "readingWord", k "RMTlibWeyl" "readingWord")] }

/-- `WeylIndex → RHWeylBasis`: rejected. The RH formalisation characterizes `ssIdx` by leading
monomials of its basis, not by RSK; the reading word has no counterpart there, and the connector
`WeylBridge` is how the two meet. -/
def weylIndexToRH : View :=
  { dom := "WeylIndex", cod := "RHWeylBasis",
    assign := [(.base "Mat", k "RHWeylBasis" "FinsuppMat"), (.base "interlaced", k "RHWeylBasis" "Interlaced")] }

/-- Statement: a Hermitian lattice with a metric at infinity, and its slope (Arakelov). -/
def arakelovLattice : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Lattice" (some type) none,
              .const "Real" (some type) none,
              .const "logIndexAtPrimes" (some (arrow (k "ArakelovLattice" "Lattice") (k "ArakelovLattice" "Real"))) none,
              .const "logCovolumeAtInfinity" (some (arrow (k "ArakelovLattice" "Lattice") (k "ArakelovLattice" "Real"))) none,
              .const "slope" (some (arrow (k "ArakelovLattice" "Lattice") (k "ArakelovLattice" "Real"))) none] }

/-- The RH formalisation's instance: the Weyl module over `ℤ` with the Fock metric
(`PI.MuStd`, `PI.stdGram`, `WeylRational`). -/
def rhArakelov : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "WeylModuleZ" (some type) none,
              .const "R" (some type) none,
              .const "weylIndex" (some (arrow (k "RHArakelov" "WeylModuleZ") (k "RHArakelov" "R"))) none,
              .const "logDetStdGram" (some (arrow (k "RHArakelov" "WeylModuleZ") (k "RHArakelov" "R"))) none,
              .const "muStd" (some (arrow (k "RHArakelov" "WeylModuleZ") (k "RHArakelov" "R"))) none] }

/-- The moment recipe's instance, as an analogy: "lattice" = the local data, the finite-place
part = `Σ_p log A_p`, the archimedean part = the conductor term. -/
def idelicMoments : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "LocalData" (some type) none,
              .const "R" (some type) none,
              .const "sumOverPrimesLogA" (some (arrow (k "IdelicMoments" "LocalData") (k "IdelicMoments" "R"))) none,
              .const "conductorTerm" (some (arrow (k "IdelicMoments" "LocalData") (k "IdelicMoments" "R"))) none,
              .const "logArithFactor" (some (arrow (k "IdelicMoments" "LocalData") (k "IdelicMoments" "R"))) none] }

def arakelovToRH : View :=
  { dom := "ArakelovLattice", cod := "RHArakelov",
    assign := [(.base "Lattice", k "RHArakelov" "WeylModuleZ"), (.base "Real", k "RHArakelov" "R"),
               (.base "logIndexAtPrimes", k "RHArakelov" "weylIndex"),
               (.base "logCovolumeAtInfinity", k "RHArakelov" "logDetStdGram"),
               (.base "slope", k "RHArakelov" "muStd")] }

def arakelovToMoments : View :=
  { dom := "ArakelovLattice", cod := "IdelicMoments",
    assign := [(.base "Lattice", k "IdelicMoments" "LocalData"), (.base "Real", k "IdelicMoments" "R"),
               (.base "logIndexAtPrimes", k "IdelicMoments" "sumOverPrimesLogA"),
               (.base "logCovolumeAtInfinity", k "IdelicMoments" "conductorTerm"),
               (.base "slope", k "IdelicMoments" "logArithFactor")] }

/-! ## Is infinity a place like the others?

`Places` is the homogeneous form of the moment recipe that the programme is after: every place,
infinity included, carries the same two pieces of local data, a kernel and a conductor. Over a
function field `𝔽_q(T)` that is literally true: infinity is a prime of degree one, with local
factor `1/(1 − q^{−1−u})`. Over `ℚ` it is not: in the recipe, the place at infinity contributes
only a conductor (`x = log(t/2π)`, plus the polygamma "times" `x_n(t)` of `scripts/`), and no
kernel. The checker makes the difference precise: the view into the function-field model is
total, the view into the ζ model is not, and its gap is exactly the missing kernel at infinity. -/

/-- Homogeneous local data: at every place a kernel and a conductor; `infinity` is a place. -/
def places : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Place" (some type) none,
              .const "Num" (some type) none,
              .const "Kernel" (some type) none,
              .const "infinity" (some (k "Places" "Place")) none,
              .const "kernel" (some (arrow (k "Places" "Place") (k "Places" "Kernel"))) none,
              .const "conductor" (some (arrow (k "Places" "Place") (k "Places" "Num"))) none,
              .const "kernelAtInfinity" (some (k "Places" "Kernel")) none] }

/-- `𝔽_q[T]` with its place at infinity (a prime of degree one). -/
def functionFieldModel : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Prime" (some type) none,
              .const "Num" (some type) none,
              .const "EulerFactor" (some type) none,
              .const "infinityPrime" (some (k "FunctionFieldModel" "Prime")) none,
              .const "localFactor" (some (arrow (k "FunctionFieldModel" "Prime") (k "FunctionFieldModel" "EulerFactor"))) none,
              .const "degree" (some (arrow (k "FunctionFieldModel" "Prime") (k "FunctionFieldModel" "Num"))) none,
              .const "factorAtInfinity" (some (k "FunctionFieldModel" "EulerFactor")) none] }

/-- `ℚ` as the recipe sees it: finite primes with Euler factors, and an archimedean place with a
conductor (Gamma factors, Stirling) but no kernel. -/
def zetaPlaces : Theory :=
  { metaThy := some "LF",
    decls := [.incl "Logic",
              .const "Place" (some type) none,
              .const "Num" (some type) none,
              .const "EulerFactor" (some type) none,
              .const "archimedean" (some (k "ZetaPlaces" "Place")) none,
              .const "localFactor" (some (arrow (k "ZetaPlaces" "Place") (k "ZetaPlaces" "EulerFactor"))) none,
              .const "logConductor" (some (arrow (k "ZetaPlaces" "Place") (k "ZetaPlaces" "Num"))) none] }

/-- `Places → FunctionFieldModel`: total; infinity is the degree-one prime. -/
def placesToFunctionField : View :=
  { dom := "Places", cod := "FunctionFieldModel",
    assign := [(.base "Place", k "FunctionFieldModel" "Prime"), (.base "Num", k "FunctionFieldModel" "Num"),
               (.base "Kernel", k "FunctionFieldModel" "EulerFactor"),
               (.base "infinity", k "FunctionFieldModel" "infinityPrime"),
               (.base "kernel", k "FunctionFieldModel" "localFactor"),
               (.base "conductor", k "FunctionFieldModel" "degree"),
               (.base "kernelAtInfinity", k "FunctionFieldModel" "factorAtInfinity")] }

/-- `Places ⇢ ZetaPlaces`: everything but the kernel at infinity. -/
def placesToZeta : View :=
  { dom := "Places", cod := "ZetaPlaces",
    assign := [(.base "Place", k "ZetaPlaces" "Place"), (.base "Num", k "ZetaPlaces" "Num"),
               (.base "Kernel", k "ZetaPlaces" "EulerFactor"),
               (.base "infinity", k "ZetaPlaces" "archimedean"),
               (.base "kernel", k "ZetaPlaces" "localFactor"),
               (.base "conductor", k "ZetaPlaces" "logConductor")] }

/-! ## The library and the checks -/

/-- The theory graph. -/
def lib : Library := fun
  | "LF" => some lfThy
  | "Recipe" => some recipe
  | "UNModel" => some unModel
  | "ZetaModel" => some zetaModel
  | "NullLattice" => some nullLattice
  | "GrowthRSK" => some growthRSK
  | "Kruskal" => some kruskal
  | "HookFact" => some hookFact
  | "RHFock" => some rhFock
  | "Logic" => some logic
  | "Complementarity" => some complementarity
  | "RMTlibComplement" => some rmtComplement
  | "WeylIndex" => some weylIndex
  | "RMTlibWeyl" => some rmtWeyl
  | "RHWeylBasis" => some rhWeyl
  | "WeylBridge" => some weylBridge
  | "ArakelovLattice" => some arakelovLattice
  | "RHArakelov" => some rhArakelov
  | "IdelicMoments" => some idelicMoments
  | "Places" => some places
  | "FunctionFieldModel" => some functionFieldModel
  | "ZetaPlaces" => some zetaPlaces
  | _ => none

/-- All theories are well-formed. -/
theorem theories_check :
    ["Recipe", "UNModel", "ZetaModel", "NullLattice", "GrowthRSK", "Kruskal", "HookFact", "RHFock",
     "Logic", "Complementarity", "RMTlibComplement", "WeylIndex", "RMTlibWeyl", "RHWeylBasis",
     "WeylBridge", "ArakelovLattice", "RHArakelov", "IdelicMoments",
     "Places", "FunctionFieldModel", "ZetaPlaces"].all
      (checkTheory lib 4) = true := by decide

/-- The legs of the spans are well-typed views. -/
theorem recipeToUN_checks : checkView lib 4 recipeToUN = true := by decide
theorem recipeToZeta_checks : checkView lib 4 recipeToZeta = true := by decide
theorem nullToGrowth_checks : checkView lib 4 nullToGrowth = true := by decide
theorem nullToKruskal_checks : checkView lib 4 nullToKruskal = true := by decide
theorem hookToRH_checks : checkView lib 4 hookToRH = true := by decide
theorem complementarityToRMT_checks : checkView lib 4 complementarityToRMT = true := by decide
theorem weylIndexToRMT_checks : checkView lib 4 weylIndexToRMT = true := by decide
theorem arakelovToRH_checks : checkView lib 4 arakelovToRH = true := by decide
theorem arakelovToMoments_checks : checkView lib 4 arakelovToMoments = true := by decide
theorem placesToFunctionField_checks : checkView lib 4 placesToFunctionField = true := by decide

theorem recipeToUN_wellTyped : recipeToUN.WellTyped LF.foundation lib := checkView_sound recipeToUN_checks
theorem hookToRH_wellTyped : hookToRH.WellTyped LF.foundation lib := checkView_sound hookToRH_checks

/-- The direct analogies are rejected as total views. -/
theorem zetaToUN_rejected : checkView lib 4 zetaToUN = false := by decide
theorem kruskalToGrowth_rejected : checkView lib 4 kruskalToGrowth = false := by decide
theorem weylIndexToRH_rejected : checkView lib 4 weylIndexToRH = false := by decide
theorem placesToZeta_rejected : checkView lib 4 placesToZeta = false := by decide

/-- The local constants of the domain of `v` that `v` leaves unassigned. -/
def unassigned (L : Library) (v : View) : List String :=
  match L v.dom with
  | some th => th.decls.filterMap fun
      | .const n _ _ => if (v.assign.lookup (.base n)).isSome then none else some n
      | _ => none
  | none => []

/-- **What does not transfer from ζ to U(N).** -/
theorem zetaToUN_gap : unassigned lib zetaToUN = ["arithFactor", "cutoffFree", "cutoffFreeThm"] := by
  decide

/-- **What does not transfer from Hawking's setting to growth diagrams.** -/
theorem kruskalToGrowth_gap : unassigned lib kruskalToGrowth = ["Coord", "kappa", "kruskalMap"] := by
  decide

/-- **What the RH formalisation does not have**: the RSK characterization of its index set. -/
theorem weylIndexToRH_gap : unassigned lib weylIndexToRH = ["recordingFixed", "readingWord"] := by
  decide

/-- **Over `ℚ`, infinity is not (yet) a place like the others**: the recipe has no kernel there. -/
theorem placesToZeta_gap : unassigned lib placesToZeta = ["kernelAtInfinity"] := by
  decide

/-! ## The edge table -/

/-- How a link of the programme is justified. -/
inductive Status
  /-- A Lean proof with standard axioms only. -/
  | proved
  /-- Checked by computation (`#guard`, `decide` on instances, or a script), not proved. -/
  | checked
  /-- Stated in Lean with `sorry`. -/
  | sorried
  /-- A structural correspondence or analogy, not a theorem. -/
  | analogy
  /-- Rejected as a total view; the gap is computed by `unassigned`. -/
  | rejected
  deriving DecidableEq, Repr

/-- A link: source, target, the MMT view if any, status, and where the evidence is. -/
structure Edge where
  /-- Source. -/
  src : String
  /-- Target. -/
  tgt : String
  /-- The view in this file, if the link is one. -/
  view : Option View
  /-- How it is justified. -/
  status : Status
  /-- Repository and file. -/
  evidence : String

/-- The programme's links. -/
def edges : List Edge :=
  [⟨"Recipe", "UNModel", some recipeToUN, .checked, "RMTlib scripts/un_test.py (k ≤ 3, exact)"⟩,
   ⟨"Recipe", "ZetaModel", some recipeToZeta, .checked,
     "RMTlib scripts/places.py, cutoff_free.py (k ≤ 3; Dehaye Thm 3 is a theorem about the recipe)"⟩,
   ⟨"ZetaModel", "UNModel", some zetaToUN, .rejected, "this file: zetaToUN_gap"⟩,
   ⟨"NullLattice", "GrowthRSK", some nullToGrowth, .proved, "RMTlib RMTlib/Growth/RSK.lean (row, localRule)"⟩,
   ⟨"NullLattice", "Kruskal", some nullToKruskal, .analogy, "discretized wave equation in null coordinates"⟩,
   ⟨"Kruskal", "GrowthRSK", some kruskalToGrowth, .rejected, "this file: kruskalToGrowth_gap"⟩,
   ⟨"HookFact", "RHFock", some hookToRH, .proved,
     "riemann-hypothesis-lean PI.HookSteps.HookNorm + RMTlib RMT.frobenius ⇒ RMT.Bridge.fockQ_hw_eq_hookProd (every shape)"⟩,
   ⟨"RMTlib ksConst", "RH fockQ (det^k)", none, .proved, "RMTlib bridge: RMT.Bridge.ksConst_mul_fockQ_sq"⟩,
   ⟨"RMTlib growth RSK", "RH ssIdx (basis of ∇(ν))", none, .checked,
     "RMTlib RMTlibExamples/Interlaced.lean (#guard); RMTlibTargets.readingWord (sorry)"⟩,
   ⟨"Dehaye Thm 3", "exclusion at |κ|+|λ| = 2k", none, .proved, "RMTlib RMTlib/Tableaux/Exclusion.lean"⟩,
   ⟨"Complementarity", "RMTlibComplement", some complementarityToRMT, .proved,
     "RMTlib RMTlib/Tableaux/Complement.lean (RMT.macdonald_1_7, RMT.lemma6)"⟩,
   ⟨"WeylIndex", "RMTlibWeyl", some weylIndexToRMT, .sorried,
     "RMTlib RMTlibTargets/Statements.lean (readingWord); #guard in RMTlibExamples/Interlaced.lean"⟩,
   ⟨"WeylIndex", "RHWeylBasis", some weylIndexToRH, .rejected, "this file: weylIndexToRH_gap"⟩,
   ⟨"WeylBridge (connector)", "RMTlibWeyl + RHWeylBasis", none, .proved,
     "RMTlib bridge/RMTlibBridge/WeylBasis.lean (RMT.Bridge.interlaced_iff, basis_of_recording)"⟩,
   ⟨"ArakelovLattice", "RHArakelov", some arakelovToRH, .analogy,
     "RH Formalism/PeriodIntegrals/HookBound.lean (PI.MuStd); vocabulary match, not a theorem"⟩,
   ⟨"ArakelovLattice", "IdelicMoments", some arakelovToMoments, .analogy,
     "RMTlib scripts/places.py (Σ_p log A_p); the idelic reading is an analogy"⟩,
   ⟨"Recipe at p", "RH cSL (Gindikin–Karpelevich)", none, .analogy,
     "cSL(p, p^{-u}) = ζ_p(u)/ζ_p(1+u); RH Divisors₂/GindikinKarpelevich.lean (FormulaGL: stated)"⟩,
   ⟨"d_κλ (Schur basis)", "RH MacdonaldWhittaker (Casselman–Shalika)", none, .analogy,
     "RH GroundTheory/AutomorphicForms/MacdonaldWhittaker.lean"⟩,
   ⟨"e^{x p₁} at ∞", "1/‖hw_λ‖²_Fock", none, .sorried,
     "‖hw_λ‖² = H(λ) proved (RMT.Bridge.fockQ_hw_eq_hookProd); missing: hook-length formula f^λ = |λ|!/H(λ)"⟩,
   ⟨"Varrin SL(2,ℝ) Plancherel", "archimedean c-function", none, .analogy, "arXiv:2610.37750; no file"⟩,
   ⟨"Places", "FunctionFieldModel", some placesToFunctionField, .analogy,
     "over 𝔽_q(T) infinity is a degree-one prime; moment recipe there not yet computed"⟩,
   ⟨"Places", "ZetaPlaces", some placesToZeta, .rejected, "this file: placesToZeta_gap"⟩,
   ⟨"Recipe at ∞", "coherent state exp(Σ x_n p_n)", none, .checked,
     "x_1 = −log(t/2π) + O(t^{−2}), x_n ~ t^{1−n} (mpmath, t ≤ 10^4)"⟩,
   ⟨"Recipe", "ZetaModel (via Theorem 3 itself)", none, .checked,
     "RMTlib scripts/theorem3_zeta.py (k = 2, agrees with the swap route to 3e-10)"⟩]

/-- Every link that is a view and claimed proved, checked or an analogy passes the checker;
every rejected one fails it. -/
theorem edges_consistent :
    edges.all (fun e => match e.view, e.status with
      | some v, .rejected => !checkView lib 4 v
      | some v, _ => checkView lib 4 v
      | none, _ => true) = true := by decide

end MMT.Atlas
