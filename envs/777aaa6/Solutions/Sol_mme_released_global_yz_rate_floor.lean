-- Prove2me | solution 1 for mme_released_global_yz_rate_floor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:17:19.707987+00:00
-- url     : https://prove2.me/submissions/8a8db535-30a3-4c8b-806d-2ac1dac4aa14

import Definitions.Def_mme_released_global_yz_certificate
import Theorems.Thm_mme_released_global_yz_data_valid
import Theorems.Thm_mme_released_global_yz_log_intervals
import Theorems.Thm_mme_released_global_yz_entropy_bridge
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.ReleasedGlobalYZ MME.GlobalCW MME.RecursiveYZ
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
attribute [local irreducible] entries rateFloor profile wordEquiv cachedCounts

theorem solution (o : Fin 6) (i : Fin 2) :
    (rateFloor o : ℝ) ≤ (profile o).coarse (yzMode i) 0 +
      (profile o).words (yzMode i) 0 - (profile o).compat i 0 := by
  have hb : (rateFloor o : ℝ) ≤ (totalBound o i : ℝ) := by
    exact_mod_cast mme_released_global_yz_data_valid.2.2 o i
  have he (e : Entry) (h : e ∈ entries o i) :
      (entryBound e : ℝ) ≤ (e.1.1 : ℝ) * Real.log (e.1.2 : ℝ) := by
    have hl := mme_released_global_yz_log_intervals o i e h
    unfold entryBound
    by_cases hc : 0 ≤ e.1.1
    · rw [if_pos hc,Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left hl.1 (by exact_mod_cast hc)
    · rw [if_neg hc,Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left hl.2 (by exact_mod_cast (le_of_lt (lt_of_not_ge hc)))
  have hs := List.sum_le_sum he
  have hc : (totalBound o i : ℝ) ≤ evaluate ((entries o i).map Prod.fst) := by
    simpa [totalBound,evaluate,List.map_map,Function.comp_def] using hs
  rw [mme_released_global_yz_entropy_bridge] at hc
  exact hb.trans hc
