-- Prove2me | solution 1 for RainbowAP.T_theta
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:31:11.598554+00:00
-- url     : https://prove2.me/submissions/dd18a0d7-d212-43ff-b363-17ca40371238

-- Sol generated from Shared/RainbowAPPairThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPPairThreshold
import Theorems.Thm_RainbowAP_T_lower_bound
import Theorems.Thm_RainbowAP_T_upper_bound

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











open RainbowAP in
theorem solution:
    ∃ c₁ c₂ : ℝ, 0.1 ≤ c₁ ∧ c₁ ≤ c₂ ∧ c₂ ≤ 10 ∧
      (∀ k : ℕ, 2 ≤ k → c₁ * ((k : ℝ) ^ 2 * Real.log k) ≤ (T k : ℝ)) ∧
      (∀ k : ℕ, 2 ≤ k → (T k : ℝ) ≤ c₂ * ((k : ℝ) ^ 2 * Real.log k)) := by
  refine ⟨1, 4, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro k hk
    have hlow := T_lower_bound k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by linarith)
    have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 - 2 := by nlinarith
    nlinarith [hlow, hlogk, mul_nonneg hk2 hlogk]
  · intro k hk
    have hup := T_upper_bound k hk
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlogk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hkR
    have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith [hup, hlog2, hlogk, hk4]
