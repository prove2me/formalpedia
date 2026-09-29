-- Prove2me | Theorems.Thm_BerggrenHarmonic_shannon_eq_log_three_iff
-- name    : BerggrenHarmonic.shannon_eq_log_three_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:15:30.876406+00:00
-- url     : https://prove2.me/theorems/eb7bba64-19f2-40da-8213-2888f4f27c11
-- title:
--   Rigidity in Gibbs' inequality.
-- statement:
--   **Rigidity in Gibbs' inequality.**  The Berggren walk has maximal entropy `log 3` exactly
--   when the three moves are equally likely.
--
--   ```lean
--   theorem BerggrenHarmonic.shannon_eq_log_three_iff(P : ProbVec) :
--       shannon P = Real.log 3 ↔ ∀ a, P.p a = 1 / 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenBoundaryEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenBoundaryEntropy.lean#L100

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

theorem BerggrenHarmonic.shannon_eq_log_three_iff(P : ProbVec) :
    shannon P = Real.log 3 ↔ ∀ a, P.p a = 1 / 3 := by sorry
