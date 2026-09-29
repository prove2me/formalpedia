-- Prove2me | solution 1 for mme_released_global_owner5_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:50:15.313706+00:00
-- url     : https://prove2.me/submissions/f8d03ddb-ecc8-43d5-a98f-b7ec76bfdc3b

import Theorems.Thm_mme_released_global_owner5_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49647854, 2487425428, 30161682257, 85580652520, 30068852496, 2518420453, 49984871, 0, 49396635, 0, 0, 0, 0, 0, 0, 49298498, 2462054477, 0, 0, 0, 0, 0, 2502852454, 29848185450, 0, 0, 0, 0, 29843118026, 85535730403, 0, 0, 0, 83899420204, 30295651400, 0, 0, 29918250959, 2562399822, 0, 2531327790, 49892168, 49891812, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 5 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 5 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49647854 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49647854 ≤ (![49647854, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49647854 : ℕ) : ℝ) ≤ ((![49647854, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2487425428 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2487425428 ≤ (![2487425428, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2487425428 : ℕ) : ℝ) ≤ ((![2487425428, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30161682257 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30161682257 ≤ (![30161682257, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30161682257 : ℕ) : ℝ) ≤ ((![30161682257, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85580652520 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85580652520 ≤ (![85580652520, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85580652520 : ℕ) : ℝ) ≤ ((![85580652520, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30068852496 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30068852496 ≤ (![30068852496, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30068852496 : ℕ) : ℝ) ≤ ((![30068852496, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2518420453 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2518420453 ≤ (![2518420453, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2518420453 : ℕ) : ℝ) ≤ ((![2518420453, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49984871 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        49984871 ≤ (![49984871, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49984871 : ℕ) : ℝ) ≤ ((![49984871, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49396635 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49396635 ≤ (![0, 49396635, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49396635 : ℕ) : ℝ) ≤ ((![0, 49396635, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((49298498 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49298498 ≤ (![0, 0, 49298498] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49298498 : ℕ) : ℝ) ≤ ((![0, 0, 49298498] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2462054477 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2462054477 ≤ (![0, 2462054477, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2462054477 : ℕ) : ℝ) ≤ ((![0, 2462054477, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((2502852454 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2502852454 ≤ (![0, 0, 2502852454] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2502852454 : ℕ) : ℝ) ≤ ((![0, 0, 2502852454] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29848185450 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29848185450 ≤ (![0, 29848185450, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29848185450 : ℕ) : ℝ) ≤ ((![0, 29848185450, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((29843118026 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29843118026 ≤ (![0, 0, 29843118026] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29843118026 : ℕ) : ℝ) ≤ ((![0, 0, 29843118026] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85535730403 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85535730403 ≤ (![0, 85535730403, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85535730403 : ℕ) : ℝ) ≤ ((![0, 85535730403, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83899420204 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83899420204 ≤ (![0, 0, 83899420204] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83899420204 : ℕ) : ℝ) ≤ ((![0, 0, 83899420204] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30295651400 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30295651400 ≤ (![0, 30295651400, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30295651400 : ℕ) : ℝ) ≤ ((![0, 30295651400, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29918250959 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29918250959 ≤ (![0, 0, 29918250959] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29918250959 : ℕ) : ℝ) ≤ ((![0, 0, 29918250959] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2562399822 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2562399822 ≤ (![0, 2562399822, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2562399822 : ℕ) : ℝ) ≤ ((![0, 2562399822, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2531327790 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2531327790 ≤ (![0, 0, 2531327790] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2531327790 : ℕ) : ℝ) ≤ ((![0, 0, 2531327790] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49892168 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        49892168 ≤ (![0, 49892168, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49892168 : ℕ) : ℝ) ≤ ((![0, 49892168, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49891812 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49891812 ≤ (![0, 0, 49891812] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49891812 : ℕ) : ℝ) ≤ ((![0, 0, 49891812] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner5_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
