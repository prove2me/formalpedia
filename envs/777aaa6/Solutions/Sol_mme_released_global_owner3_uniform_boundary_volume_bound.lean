-- Prove2me | solution 1 for mme_released_global_owner3_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:16:50.959459+00:00
-- url     : https://prove2.me/submissions/41468941-0277-4353-bde0-097543bde991

import Theorems.Thm_mme_released_global_owner3_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49668638, 2487054614, 30163457323, 85576822698, 30067821815, 2517127730, 49831181, 0, 49330957, 0, 0, 0, 0, 0, 0, 49418204, 2462068005, 0, 0, 0, 0, 0, 2503068561, 29847084297, 0, 0, 0, 0, 29843979565, 85531596254, 0, 0, 0, 83903297232, 30295951027, 0, 0, 29916676812, 2563402632, 0, 2532342617, 49928473, 49653342, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 3 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 3 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49668638 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49668638 ≤ (![49668638, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49668638 : ℕ) : ℝ) ≤ ((![49668638, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2487054614 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2487054614 ≤ (![2487054614, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2487054614 : ℕ) : ℝ) ≤ ((![2487054614, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30163457323 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30163457323 ≤ (![30163457323, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30163457323 : ℕ) : ℝ) ≤ ((![30163457323, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85576822698 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85576822698 ≤ (![85576822698, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85576822698 : ℕ) : ℝ) ≤ ((![85576822698, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30067821815 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30067821815 ≤ (![30067821815, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30067821815 : ℕ) : ℝ) ≤ ((![30067821815, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2517127730 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2517127730 ≤ (![2517127730, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2517127730 : ℕ) : ℝ) ≤ ((![2517127730, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49831181 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        49831181 ≤ (![49831181, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49831181 : ℕ) : ℝ) ≤ ((![49831181, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49330957 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49330957 ≤ (![0, 49330957, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49330957 : ℕ) : ℝ) ≤ ((![0, 49330957, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((49418204 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49418204 ≤ (![0, 0, 49418204] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49418204 : ℕ) : ℝ) ≤ ((![0, 0, 49418204] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2462068005 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2462068005 ≤ (![0, 2462068005, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2462068005 : ℕ) : ℝ) ≤ ((![0, 2462068005, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((2503068561 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2503068561 ≤ (![0, 0, 2503068561] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2503068561 : ℕ) : ℝ) ≤ ((![0, 0, 2503068561] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29847084297 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29847084297 ≤ (![0, 29847084297, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29847084297 : ℕ) : ℝ) ≤ ((![0, 29847084297, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((29843979565 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29843979565 ≤ (![0, 0, 29843979565] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29843979565 : ℕ) : ℝ) ≤ ((![0, 0, 29843979565] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85531596254 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85531596254 ≤ (![0, 85531596254, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85531596254 : ℕ) : ℝ) ≤ ((![0, 85531596254, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83903297232 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83903297232 ≤ (![0, 0, 83903297232] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83903297232 : ℕ) : ℝ) ≤ ((![0, 0, 83903297232] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30295951027 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30295951027 ≤ (![0, 30295951027, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30295951027 : ℕ) : ℝ) ≤ ((![0, 30295951027, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29916676812 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29916676812 ≤ (![0, 0, 29916676812] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29916676812 : ℕ) : ℝ) ≤ ((![0, 0, 29916676812] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2563402632 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2563402632 ≤ (![0, 2563402632, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2563402632 : ℕ) : ℝ) ≤ ((![0, 2563402632, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2532342617 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2532342617 ≤ (![0, 0, 2532342617] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2532342617 : ℕ) : ℝ) ≤ ((![0, 0, 2532342617] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49928473 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        49928473 ≤ (![0, 49928473, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49928473 : ℕ) : ℝ) ≤ ((![0, 49928473, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49653342 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49653342 ≤ (![0, 0, 49653342] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49653342 : ℕ) : ℝ) ≤ ((![0, 0, 49653342] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner3_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
