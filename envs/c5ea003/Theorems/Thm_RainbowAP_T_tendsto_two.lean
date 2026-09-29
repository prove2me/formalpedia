-- Prove2me | Theorems.Thm_RainbowAP_T_tendsto_two
-- name    : RainbowAP.T_tendsto_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:16.439498+00:00
-- url     : https://prove2.me/theorems/8352a6db-8cbb-4e95-9271-d539adc1960d
-- title:
--   The exact asymptotic constant: `T k / (kÂ² log k) â 2`.
-- statement:
--   The exact asymptotic constant: `T k / (kÂ² log k) â 2`.
--
--   ```lean
--   theorem RainbowAP.T_tendsto_two:
--       Tendsto (fun k : ℕ => (T k : ℝ) / ((k : ℝ) ^ 2 * Real.log k)) atTop (𝓝 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPPairThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPPairThreshold.lean#L97

-- Thm stub generated from Shared/RainbowAPPairThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPPairThreshold

/-!
# The rainbow pair-spectrum threshold `T_k` and its exact `Θ(k² log k)` growth

Fix a palette of `k` colours.  A colouring of a block-decomposed interval realises the
*full pair spectrum* if every one of the `k²` ordered colour pairs `(i, j)` occurs on some
2-term arithmetic progression of the decomposition.  `T k` is the least number of blocks at
which a strict majority of colourings has full pair spectrum; formally it is the full-spectrum
threshold of the alphabet `Fin k × Fin k`.

Main results.

* `RainbowAP.T_lower_bound` : `2 k² log k - 2 log k ≤ T k`.
* `RainbowAP.T_upper_bound` : `T k ≤ 2 k² log k + k² log 2 + 1`.
* `RainbowAP.T_theta`       : explicit constants `c₁ = 1`, `c₂ = 4` with
  `0.1 ≤ c₁ ≤ c₂ ≤ 10` sandwiching `T k` between `c₁ k² log k` and `c₂ k² log k` for `k ≥ 2`.
* `RainbowAP.T_tendsto_two` : `T k / (k² log k) → 2`, so the optimal constants coincide,
  `c₁ = c₂ = 2`.
* `RainbowAP.T_liminf`, `RainbowAP.T_limsup` : the `lim inf` and the `lim sup` both equal `2`.
-/

open Finset Real Filter Topology

open RainbowAP

theorem RainbowAP.T_tendsto_two:
    Tendsto (fun k : ℕ => (T k : ℝ) / ((k : ℝ) ^ 2 * Real.log k)) atTop (𝓝 2) := by sorry
