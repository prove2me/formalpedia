-- Prove2me | Theorems.Thm_RainbowAP_T_lower_bound
-- name    : RainbowAP.T_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:08.762283+00:00
-- url     : https://prove2.me/theorems/575969ac-334f-4300-b3a3-0ce64153f892
-- title:
--   Lower bound: `T k â¥ 2 kÂ² log k - 2 log k`.
-- statement:
--   **Lower bound**: `T k â¥ 2 kÂ² log k - 2 log k`.
--
--   ```lean
--   theorem RainbowAP.T_lower_bound(k : ℕ) (hk : 2 ≤ k) :
--       2 * (k : ℝ) ^ 2 * Real.log k - 2 * Real.log k ≤ (T k : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPPairThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPPairThreshold.lean#L37

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

theorem RainbowAP.T_lower_bound(k : ℕ) (hk : 2 ≤ k) :
    2 * (k : ℝ) ^ 2 * Real.log k - 2 * Real.log k ≤ (T k : ℝ) := by sorry
