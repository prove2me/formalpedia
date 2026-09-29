-- Prove2me | solution 1 for mme_released_global_x_rate_floor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T12:02:36.461993+00:00
-- url     : https://prove2.me/submissions/79df76e9-b662-46ba-9984-7772c1d366b1

import Definitions.Def_mme_released_global_x_certificate
import Theorems.Thm_mme_released_global_x_data_valid
import Theorems.Thm_mme_released_global_x_log_intervals
import Theorems.Thm_mme_released_global_x_entropy_bridge
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1600000
attribute [local irreducible] alphaQ marginalQ dualQ rateFloor xLogLower xLogUpper

theorem solution (o : Fin 6) :
    (rateFloor o : ℝ) ≤ (profile o).coarse 0 0 -
      Real.log 2 * entropyPenalty ((profile o).1 0) := by
  rcases mme_released_global_x_data_valid with ⟨hA,hAm,hMm,hd,hT,hDm,hD,hM,hlogA,hlogD,hlogM,hF⟩
  have ha (s : Fin 45) : -((alphaQ o s : ℝ)*(xLogUpper o ⟨s.val,by omega⟩ : ℝ)) ≤
      Real.negMulLog (alphaQ o s : ℝ) := by
    have h := (mme_released_global_x_log_intervals o ⟨s.val,by omega⟩).2
    rw [hlogA] at h
    have hp : (0 : ℝ) ≤ (alphaQ o s : ℝ) := by exact_mod_cast hA o s
    have hh := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hp)
    simpa [Real.negMulLog] using hh
  have hm (j : Fin 9) : -((marginalQ o 0 j : ℝ)*(xLogUpper o ⟨90+j.val,by omega⟩ : ℝ)) ≤
      Real.negMulLog (marginalQ o 0 j : ℝ) := by
    have h := (mme_released_global_x_log_intervals o ⟨90+j.val,by omega⟩).2
    rw [hlogM] at h
    have hp : (0 : ℝ) ≤ (marginalQ o 0 j : ℝ) := by exact_mod_cast hM o j
    have hh := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hp)
    simpa [Real.negMulLog] using hh
  have hd (s : Fin 45) : (alphaQ o s : ℝ)*(xLogLower o ⟨45+s.val,by omega⟩ : ℝ) ≤
      (alphaQ o s : ℝ)*Real.log (dualQ o s : ℝ) := by
    have h := (mme_released_global_x_log_intervals o ⟨45+s.val,by omega⟩).1
    rw [hlogD] at h
    exact mul_le_mul_of_nonneg_left h (by exact_mod_cast hA o s)
  have hsa := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 45))) ↦ ha s)
  have hsm := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 9))) ↦ hm j)
  have hsd := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 45))) ↦ hd s)
  have hf : (rateFloor o : ℝ) ≤ (xBound o : ℝ) := by exact_mod_cast hF o
  have hb := mme_released_global_x_entropy_bridge o
  unfold xBound at hf
  push_cast at hf
  rw [Finset.sum_neg_distrib] at hsa hsm
  rw [hb.2.1]
  rw [hb.2.2] at hb
  linarith [hb.1]
