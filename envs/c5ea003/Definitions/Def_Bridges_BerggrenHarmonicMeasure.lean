-- Prove2me | Definitions.Def_Bridges_BerggrenHarmonicMeasure
-- name    : Bridges_BerggrenHarmonicMeasure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:56.699718+00:00
-- url     : https://prove2.me/theorems/ec118459-7c96-4258-b660-c1c2053a924f
-- title:
--   Aether Catalog definitions — Bridges_BerggrenHarmonicMeasure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenHarmonicMeasure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenHarmonicMeasure.lean by skeleton subtraction
import Mathlib

/-!
# Harmonic measure on the boundary of the Berggren tree

The Berggren tree of primitive Pythagorean triples is the free rooted ternary tree on the
three Berggren moves `L, M, R` (the catalog's `HyperbolicBerggrenGeodesics.Move`, whose
words `run : List Move → ℕ × ℕ` enumerate every primitive triple exactly once).  Its
*boundary* — the set of infinite descending paths — is therefore the space of infinite words
over a three letter alphabet,

`Bdry = ℕ → Fin 3`,

the **3-adic Cantor set**.  This file develops the probabilistic theory of the tree:

* `cyl n v` : the cylinder set of boundary points agreeing with `v` on the first `n` letters
  (the shadow of a depth-`n` node of the tree).
* `ProbVec` : a strictly positive probability vector `(p₁, p₂, p₃)` on the three moves.
* `bernoulli P` : the Bernoulli (product) measure on the boundary, built with Mathlib's
  infinite product measure `MeasureTheory.Measure.infinitePi`.
* `IsHarmonic P ν` : the *harmonicity* (stationarity, self-similarity) equation
  `ν = ∑ a, pₐ · (consₐ)_* ν` characterising the hitting distribution on the boundary of the
  random walk which, at each step, appends the letter `a` with probability `pₐ`.

## Main results

* `bernoulli_cyl` : the product measure of a depth-`n` cylinder is `∏_{i<n} p_{v i}`.
* `ext_of_cyl_eq` : two probability measures on the boundary agreeing on all cylinders are
  equal (the cylinders form a π-system generating the product σ-algebra:
  `isPiSystem_cylinders`, `generateFrom_cylinders`).
* `IsHarmonic.cyl_eq` : *every* harmonic measure gives a cylinder its Bernoulli mass.
* `bernoulli_isHarmonic` : the Bernoulli measure is harmonic.
* `harmonic_iff_bernoulli`, `existsUnique_harmonic` : **the harmonic measure of the Berggren
  random walk exists, is unique, and is exactly the Bernoulli product measure** — the main
  conjecture of this cycle, in the strong "unique stationary measure" form.
* `bernoulli_uniform_cyl` : for the uniform walk the harmonic measure of a depth-`n`
  cylinder is `3^{-n}`, i.e. it is the Hausdorff/Cantor measure of the 3-adic boundary.
-/

namespace BerggrenHarmonic

open MeasureTheory Set MeasurableSpace
open scoped ENNReal

/-- The three Berggren moves, as an alphabet.  (`0 ↔ L`, `1 ↔ M`, `2 ↔ R` for the catalog's
`HyperbolicBerggrenGeodesics.Move`.) -/
abbrev Letter := Fin 3

/-- The boundary of the Berggren tree: infinite words in the three moves, i.e. the 3-adic
Cantor set. -/
abbrev Bdry := ℕ → Letter

/-- The cylinder set of depth `n` through `v`: all boundary points whose first `n` letters
agree with those of `v`.  This is the shadow of the depth-`n` node `run (v 0 :: … :: v (n-1))`
of the Berggren tree. -/
def cyl (n : ℕ) (v : Bdry) : Set Bdry := {x | ∀ i < n, x i = v i}

/-- Prepending a letter: the boundary map induced by the Berggren move `a`. -/
def cons (a : Letter) (x : Bdry) : Bdry
  | 0 => a
  | (k + 1) => x k







/-- The shift of a word. -/
def tail (v : Bdry) : Bdry := fun k => v (k + 1)


/-! ## Probability vectors and the Bernoulli measure -/

/-- A strictly positive probability vector on the three Berggren moves. -/
structure ProbVec where
  /-- the weights -/
  p : Letter → ℝ
  /-- strict positivity -/
  pos : ∀ a, 0 < p a
  /-- normalisation -/
  sum_eq : ∑ a, p a = 1

namespace ProbVec

variable (P : ProbVec)


/-- The one-step distribution of the walk, as a `PMF` on the three moves. -/
noncomputable def pmf : PMF Letter :=
  PMF.ofFintype (fun a => ENNReal.ofReal (P.p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (P.pos a).le), P.sum_eq, ENNReal.ofReal_one])


/-- The one-step distribution as a measure on the alphabet. -/
noncomputable def stepMeasure : Measure Letter := P.pmf.toMeasure

instance : IsProbabilityMeasure P.stepMeasure := by
  unfold stepMeasure; infer_instance


end ProbVec

/-- The Bernoulli (product) measure on the 3-adic boundary attached to the weights `P`. -/
noncomputable def bernoulli (P : ProbVec) : Measure Bdry :=
  Measure.infinitePi (fun _ : ℕ => P.stepMeasure)

instance (P : ProbVec) : IsProbabilityMeasure (bernoulli P) := by
  unfold bernoulli; infer_instance

/-- The mass a probability vector assigns to a depth-`n` cylinder. -/
noncomputable def wmass (P : ProbVec) (n : ℕ) (v : Bdry) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, ENNReal.ofReal (P.p (v i))




/-! ## Cylinders generate: a uniqueness tool -/

/-- The collection of all cylinder sets. -/
def cylinders : Set (Set Bdry) := {S | ∃ n v, S = cyl n v}




/-- Extend a finite word to an infinite one by padding with the letter `0`. -/
def extend (n : ℕ) (u : Fin n → Letter) : Bdry := fun k => if h : k < n then u ⟨k, h⟩ else 0




/-! ## Harmonicity -/

/-- **The harmonicity (stationarity) equation.**  The hitting measure of the random walk that
appends the Berggren move `a` with probability `pₐ` must satisfy
`ν = ∑ₐ pₐ · (consₐ)_* ν`: conditioning on the first move decomposes the boundary into the
three shadows of the children of the root. -/
def IsHarmonic (P : ProbVec) (ν : Measure Bdry) : Prop :=
  ν = ∑ a : Letter, ENNReal.ofReal (P.p a) • ν.map (cons a)






/-! ## The uniform walk and the Cantor measure -/

/-- The uniform (fair) Berggren walk. -/
noncomputable def uniformVec : ProbVec where
  p := fun _ => 1 / 3
  pos := fun _ => by norm_num
  sum_eq := by norm_num


end BerggrenHarmonic


