-- Prove2me | Definitions.Def_Bridges_BerggrenBoundaryEntropy
-- name    : Bridges_BerggrenBoundaryEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:39.102245+00:00
-- url     : https://prove2.me/theorems/bd7bc40a-760a-4b85-a715-bd26e7a8f864
-- title:
--   Aether Catalog definitions — Bridges_BerggrenBoundaryEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenBoundaryEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenBoundaryEntropy.lean by skeleton subtraction
import Mathlib
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

namespace BerggrenHarmonic

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

/-! ## Surprisal and Shannon entropy -/

/-- The surprisal (information content) of a Berggren move. -/
noncomputable def surp (P : ProbVec) (a : Letter) : ℝ := -Real.log (P.p a)

/-- The Shannon entropy of the step distribution of the Berggren walk. -/
noncomputable def shannon (P : ProbVec) : ℝ := -∑ a, P.p a * Real.log (P.p a)











/-! ## Cylinder masses in the reals -/

/-- The real-valued mass of the depth-`n` cylinder through `v`. -/
noncomputable def massR (P : ProbVec) (n : ℕ) (v : Bdry) : ℝ :=
  ∏ i ∈ Finset.range n, P.p (v i)




/-! ## The exact level-`n` entropy identity -/



/-! ## Shannon–McMillan–Breiman on the Berggren boundary -/










/-! ## Dimension -/

/-- The dimension of the harmonic measure: entropy divided by the logarithm of the branching
number.  With the natural 3-adic metric on the boundary (`diam (cyl n x) = 3⁻ⁿ`) this is the
pointwise dimension of the measure. -/
noncomputable def dimH (P : ProbVec) : ℝ := shannon P / Real.log 3







end BerggrenHarmonic


