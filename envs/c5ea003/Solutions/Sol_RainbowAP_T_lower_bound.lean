-- Prove2me | solution 1 for RainbowAP.T_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:26:40.301972+00:00
-- url     : https://prove2.me/submissions/4920587d-4245-42fc-bf06-afb3e27a8642

-- Sol generated from Shared/RainbowAPPairThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPPairThreshold
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_card_pair_alphabet
import Theorems.Thm_RainbowAP_card_pair_alphabet_ge
import Theorems.Thm_RainbowAP_le_spectrumThreshold

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
theorem solution(k : ℕ) (hk : 2 ≤ k) :
    2 * (k : ℝ) ^ 2 * Real.log k - 2 * Real.log k ≤ (T k : ℝ) := by
  rw [T]
  have hbase := le_spectrumThreshold (α := Fin k × Fin k) (card_pair_alphabet_ge k hk)
  rw [card_pair_alphabet] at hbase
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ ((k : ℝ)) ^ 2 - 1 := by nlinarith
  have hlogk : (0 : ℝ) ≤ Real.log k := Real.log_nonneg (by linarith)
  have hlog : 2 * Real.log k ≤ Real.log (((k : ℝ) ^ 2) + 1) := by
    have h1 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log k := by
      rw [Real.log_pow]
      push_cast
      ring
    have h2 : Real.log ((k : ℝ) ^ 2) ≤ Real.log (((k : ℝ) ^ 2) + 1) := by
      apply Real.log_le_log (by positivity)
      linarith
    linarith
  have hcast : ((((k ^ 2 : ℕ)) : ℝ)) = ((k : ℝ)) ^ 2 := by push_cast; ring
  rw [hcast] at hbase
  nlinarith [hbase, hlog, hk2, hlogk]
