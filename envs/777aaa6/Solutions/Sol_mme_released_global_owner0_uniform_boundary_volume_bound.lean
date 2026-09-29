-- Prove2me | solution 1 for mme_released_global_owner0_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:22:27.838815+00:00
-- url     : https://prove2.me/submissions/e6d9cf8e-240c-42c7-9f4b-b999f5fad108

import Theorems.Thm_mme_released_global_owner0_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49606893, 2486788621, 30163129815, 85574225979, 30069522158, 2518371893, 50007291, 0, 49279954, 0, 0, 0, 0, 0, 0, 49221705, 2462660104, 0, 0, 0, 0, 0, 2502501836, 29847986703, 0, 0, 0, 0, 29841607991, 85529917414, 0, 0, 0, 83916707382, 30295306029, 0, 0, 29916765458, 2562729051, 0, 2532605850, 50115012, 49741369, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 0 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 0 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49606893 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49606893 ≤ (![49606893, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49606893 : ℕ) : ℝ) ≤ ((![49606893, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2486788621 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2486788621 ≤ (![2486788621, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2486788621 : ℕ) : ℝ) ≤ ((![2486788621, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30163129815 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30163129815 ≤ (![30163129815, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30163129815 : ℕ) : ℝ) ≤ ((![30163129815, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85574225979 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85574225979 ≤ (![85574225979, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85574225979 : ℕ) : ℝ) ≤ ((![85574225979, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30069522158 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30069522158 ≤ (![30069522158, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30069522158 : ℕ) : ℝ) ≤ ((![30069522158, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2518371893 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2518371893 ≤ (![2518371893, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2518371893 : ℕ) : ℝ) ≤ ((![2518371893, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((50007291 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        50007291 ≤ (![50007291, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((50007291 : ℕ) : ℝ) ≤ ((![50007291, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49279954 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49279954 ≤ (![0, 49279954, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49279954 : ℕ) : ℝ) ≤ ((![0, 49279954, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((49221705 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49221705 ≤ (![0, 0, 49221705] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49221705 : ℕ) : ℝ) ≤ ((![0, 0, 49221705] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2462660104 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2462660104 ≤ (![0, 2462660104, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2462660104 : ℕ) : ℝ) ≤ ((![0, 2462660104, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((2502501836 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2502501836 ≤ (![0, 0, 2502501836] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2502501836 : ℕ) : ℝ) ≤ ((![0, 0, 2502501836] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29847986703 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29847986703 ≤ (![0, 29847986703, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29847986703 : ℕ) : ℝ) ≤ ((![0, 29847986703, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((29841607991 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29841607991 ≤ (![0, 0, 29841607991] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29841607991 : ℕ) : ℝ) ≤ ((![0, 0, 29841607991] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85529917414 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85529917414 ≤ (![0, 85529917414, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85529917414 : ℕ) : ℝ) ≤ ((![0, 85529917414, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83916707382 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83916707382 ≤ (![0, 0, 83916707382] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83916707382 : ℕ) : ℝ) ≤ ((![0, 0, 83916707382] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30295306029 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30295306029 ≤ (![0, 30295306029, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30295306029 : ℕ) : ℝ) ≤ ((![0, 30295306029, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29916765458 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29916765458 ≤ (![0, 0, 29916765458] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29916765458 : ℕ) : ℝ) ≤ ((![0, 0, 29916765458] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2562729051 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2562729051 ≤ (![0, 2562729051, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2562729051 : ℕ) : ℝ) ≤ ((![0, 2562729051, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2532605850 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2532605850 ≤ (![0, 0, 2532605850] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2532605850 : ℕ) : ℝ) ≤ ((![0, 0, 2532605850] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((50115012 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        50115012 ≤ (![0, 50115012, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((50115012 : ℕ) : ℝ) ≤ ((![0, 50115012, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49741369 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49741369 ≤ (![0, 0, 49741369] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49741369 : ℕ) : ℝ) ≤ ((![0, 0, 49741369] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner0_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
