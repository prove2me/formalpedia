-- Prove2me | solution 1 for mme_released_global_owner4_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:31:56.270395+00:00
-- url     : https://prove2.me/submissions/4123a0e4-6405-4042-a899-fb7f371bcb4f

import Theorems.Thm_mme_released_global_owner4_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49711049, 2486699145, 30158552205, 85573552848, 30073749198, 2518160978, 49964227, 0, 49385212, 0, 0, 0, 0, 0, 0, 49309756, 2461960971, 0, 0, 0, 0, 0, 2502955864, 29853036253, 0, 0, 0, 0, 29838417750, 85528069838, 0, 0, 0, 83902935981, 30289370898, 0, 0, 29921870728, 2563482978, 0, 2532716737, 50113951, 49674360, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 4 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 4 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49711049 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49711049 ≤ (![49711049, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49711049 : ℕ) : ℝ) ≤ ((![49711049, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2486699145 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2486699145 ≤ (![2486699145, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2486699145 : ℕ) : ℝ) ≤ ((![2486699145, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30158552205 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30158552205 ≤ (![30158552205, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30158552205 : ℕ) : ℝ) ≤ ((![30158552205, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85573552848 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85573552848 ≤ (![85573552848, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85573552848 : ℕ) : ℝ) ≤ ((![85573552848, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30073749198 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30073749198 ≤ (![30073749198, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30073749198 : ℕ) : ℝ) ≤ ((![30073749198, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2518160978 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2518160978 ≤ (![2518160978, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2518160978 : ℕ) : ℝ) ≤ ((![2518160978, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49964227 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        49964227 ≤ (![49964227, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49964227 : ℕ) : ℝ) ≤ ((![49964227, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49385212 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49385212 ≤ (![0, 49385212, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49385212 : ℕ) : ℝ) ≤ ((![0, 49385212, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 10).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 11).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 12).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 13).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 14).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 15).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((49309756 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49309756 ≤ (![0, 0, 49309756] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49309756 : ℕ) : ℝ) ≤ ((![0, 0, 49309756] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2461960971 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2461960971 ≤ (![0, 2461960971, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2461960971 : ℕ) : ℝ) ≤ ((![0, 2461960971, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 18).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 19).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 20).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 21).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 22).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2502955864 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2502955864 ≤ (![0, 0, 2502955864] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2502955864 : ℕ) : ℝ) ≤ ((![0, 0, 2502955864] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29853036253 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29853036253 ≤ (![0, 29853036253, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29853036253 : ℕ) : ℝ) ≤ ((![0, 29853036253, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 25).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 26).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 27).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 28).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29838417750 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29838417750 ≤ (![0, 0, 29838417750] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29838417750 : ℕ) : ℝ) ≤ ((![0, 0, 29838417750] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85528069838 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85528069838 ≤ (![0, 85528069838, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85528069838 : ℕ) : ℝ) ≤ ((![0, 85528069838, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83902935981 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83902935981 ≤ (![0, 0, 83902935981] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83902935981 : ℕ) : ℝ) ≤ ((![0, 0, 83902935981] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30289370898 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30289370898 ≤ (![0, 30289370898, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30289370898 : ℕ) : ℝ) ≤ ((![0, 30289370898, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29921870728 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29921870728 ≤ (![0, 0, 29921870728] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29921870728 : ℕ) : ℝ) ≤ ((![0, 0, 29921870728] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2563482978 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2563482978 ≤ (![0, 2563482978, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2563482978 : ℕ) : ℝ) ≤ ((![0, 2563482978, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2532716737 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2532716737 ≤ (![0, 0, 2532716737] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2532716737 : ℕ) : ℝ) ≤ ((![0, 0, 2532716737] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((50113951 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        50113951 ≤ (![0, 50113951, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((50113951 : ℕ) : ℝ) ≤ ((![0, 50113951, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49674360 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49674360 ≤ (![0, 0, 49674360] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49674360 : ℕ) : ℝ) ≤ ((![0, 0, 49674360] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner4_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
