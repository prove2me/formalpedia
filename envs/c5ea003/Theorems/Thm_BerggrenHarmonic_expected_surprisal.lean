-- Prove2me | Theorems.Thm_BerggrenHarmonic_expected_surprisal
-- name    : BerggrenHarmonic.expected_surprisal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:14:49.639176+00:00
-- url     : https://prove2.me/theorems/443b6ee3-5d9f-4dbc-91e2-f583afbde5e1
-- title:
--   The mean surprisal of a depth-`n` cylinder is exactly `n · H(p)`.
-- statement:
--   **The mean surprisal of a depth-`n` cylinder is exactly `n · H(p)`.**  Summing over all
--   `3ⁿ` words of length `n`, weighted by their harmonic measure, the information content of a
--   depth-`n` node of the Berggren tree is exactly `n` times the Shannon entropy of the step
--   distribution.  This is an identity, not an asymptotic.
--
--   ```lean
--   theorem BerggrenHarmonic.expected_surprisal(P : ProbVec) (n : ℕ) :
--       ∑ w : Fin n → Letter, (∏ i, P.p (w i)) * (-Real.log (∏ i, P.p (w i)))
--         = n * shannon P := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenBoundaryEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenBoundaryEntropy.lean#L157

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

theorem BerggrenHarmonic.expected_surprisal(P : ProbVec) (n : ℕ) :
    ∑ w : Fin n → Letter, (∏ i, P.p (w i)) * (-Real.log (∏ i, P.p (w i)))
      = n * shannon P := by sorry
