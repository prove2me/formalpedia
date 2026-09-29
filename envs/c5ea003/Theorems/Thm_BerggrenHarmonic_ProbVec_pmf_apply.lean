-- Prove2me | Theorems.Thm_BerggrenHarmonic_ProbVec_pmf_apply
-- name    : BerggrenHarmonic.ProbVec.pmf_apply
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:16:34.905328+00:00
-- url     : https://prove2.me/theorems/2fbec6fb-d8c8-4968-88e0-cea7431af0cc
-- title:
--   Pmf apply
-- statement:
--   Formal statement of `BerggrenHarmonic.ProbVec.pmf_apply` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BerggrenHarmonic.ProbVec.pmf_apply(a : Letter) : P.pmf a = ENNReal.ofReal (P.p a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenHarmonicMeasure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenHarmonicMeasure.lean#L140

-- Thm stub generated from Bridges/BerggrenHarmonicMeasure.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenHarmonicMeasure

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

open BerggrenHarmonic

open MeasureTheory Set MeasurableSpace
open scoped ENNReal













/-! ## Probability vectors and the Bernoulli measure -/


open ProbVec

variable (P : ProbVec)



@[simp]

theorem BerggrenHarmonic.ProbVec.pmf_apply(a : Letter) : P.pmf a = ENNReal.ofReal (P.p a) := by sorry
