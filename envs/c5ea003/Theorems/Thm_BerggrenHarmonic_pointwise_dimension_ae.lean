-- Prove2me | Theorems.Thm_BerggrenHarmonic_pointwise_dimension_ae
-- name    : BerggrenHarmonic.pointwise_dimension_ae
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:14:57.097728+00:00
-- url     : https://prove2.me/theorems/1092f9a2-c47a-4b9d-ab40-3ccff6ce1499
-- title:
--   The pointwise dimension of the harmonic measure.
-- statement:
--   **The pointwise dimension of the harmonic measure.**  Measuring cylinders by their 3-adic
--   diameter `3⁻ⁿ`, almost every boundary point has local dimension exactly `H(p)/log 3`.
--
--   ```lean
--   theorem BerggrenHarmonic.pointwise_dimension_ae(P : ProbVec) :
--       ∀ᵐ x ∂(bernoulli P),
--         Tendsto (fun n : ℕ =>
--             Real.log ((bernoulli P (cyl n x)).toReal) / Real.log ((3 : ℝ) ^ (-(n : ℝ)))) atTop
--           (𝓝 (dimH P)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenBoundaryEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenBoundaryEntropy.lean#L316

-- Thm stub generated from Bridges/BerggrenBoundaryEntropy.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenBoundaryEntropy
import Definitions.Def_Bridges_BerggrenHarmonicMeasure

/-!
# Entropy and dimension of the harmonic measure on the Berggren boundary

Building on `Catalog.Bridges.BerggrenHarmonicMeasure`, where the harmonic measure of the
Berggren random walk was identified with the Bernoulli product measure `bernoulli P` on the
3-adic boundary `Bdry = ℕ → Fin 3`, this file computes its **entropy** and its **pointwise
(Billingsley) dimension**.

## Main results

* `shannon` : the Shannon entropy `H(p₁,p₂,p₃) = -∑ pₐ log pₐ` of the step distribution.
* `expected_surprisal` : the *exact* level-`n` identity
  `∑_{w ∈ {1,2,3}ⁿ} μ[w] · (-log μ[w]) = n · H(p)`.  The mean surprisal of a depth-`n`
  cylinder is exactly `n H(p)` — no error term.
* `shannon_le_log_three`, `shannon_eq_log_three_iff` : `H(p) ≤ log 3` with equality exactly
  for the fair walk, so the harmonic measure has full dimension iff the three Berggren moves
  are equally likely.
* `strongLaw_surprisal`, `smb_ae` : the Shannon–McMillan–Breiman theorem for the Berggren
  boundary: `μ`-almost every boundary point `x` satisfies `-(1/n) log μ(cyl n x) → H(p)`.
* `pointwise_dimension_ae` : consequently the pointwise dimension of the harmonic measure
  with respect to the natural 3-adic metric (`diam (cyl n x) = 3⁻ⁿ`) is almost surely the
  constant `dimH P = H(p)/log 3 ∈ (0, 1]`.
* `dim_le_one`, `dim_uniform_eq_one`, `dim_eq_one_iff` : the dimension is at most `1`, the
  dimension of the whole 3-adic Cantor boundary, with equality iff the walk is fair.
-/

open BerggrenHarmonic

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

/-! ## Surprisal and Shannon entropy -/













/-! ## Cylinder masses in the reals -/





/-! ## The exact level-`n` entropy identity -/



/-! ## Shannon–McMillan–Breiman on the Berggren boundary -/










/-! ## Dimension -/

theorem BerggrenHarmonic.pointwise_dimension_ae(P : ProbVec) :
    ∀ᵐ x ∂(bernoulli P),
      Tendsto (fun n : ℕ =>
          Real.log ((bernoulli P (cyl n x)).toReal) / Real.log ((3 : ℝ) ^ (-(n : ℝ)))) atTop
        (𝓝 (dimH P)) := by sorry
