-- Prove2me | solution 1 for mme_released_global_owner1_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:41:09.311712+00:00
-- url     : https://prove2.me/submissions/db0cb653-c561-447c-bb82-22cce92868d1

import Theorems.Thm_mme_released_global_owner1_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49820906, 2487243242, 30161916128, 85578723810, 30067934123, 2518649441, 49990101, 0, 49245656, 0, 0, 0, 0, 0, 0, 49294690, 2462639231, 0, 0, 0, 0, 0, 2501614000, 29848152952, 0, 0, 0, 0, 29843357938, 85534235882, 0, 0, 0, 83900425454, 30294238639, 0, 0, 29918440055, 2562591995, 0, 2532957755, 50087514, 49684414, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 1 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 1 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49820906 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49820906 ≤ (![49820906, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49820906 : ℕ) : ℝ) ≤ ((![49820906, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2487243242 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2487243242 ≤ (![2487243242, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2487243242 : ℕ) : ℝ) ≤ ((![2487243242, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30161916128 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30161916128 ≤ (![30161916128, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30161916128 : ℕ) : ℝ) ≤ ((![30161916128, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85578723810 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85578723810 ≤ (![85578723810, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85578723810 : ℕ) : ℝ) ≤ ((![85578723810, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30067934123 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30067934123 ≤ (![30067934123, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30067934123 : ℕ) : ℝ) ≤ ((![30067934123, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2518649441 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2518649441 ≤ (![2518649441, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2518649441 : ℕ) : ℝ) ≤ ((![2518649441, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49990101 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        49990101 ≤ (![49990101, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49990101 : ℕ) : ℝ) ≤ ((![49990101, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49245656 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49245656 ≤ (![0, 49245656, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49245656 : ℕ) : ℝ) ≤ ((![0, 49245656, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((49294690 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49294690 ≤ (![0, 0, 49294690] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49294690 : ℕ) : ℝ) ≤ ((![0, 0, 49294690] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2462639231 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2462639231 ≤ (![0, 2462639231, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2462639231 : ℕ) : ℝ) ≤ ((![0, 2462639231, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((2501614000 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2501614000 ≤ (![0, 0, 2501614000] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2501614000 : ℕ) : ℝ) ≤ ((![0, 0, 2501614000] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29848152952 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29848152952 ≤ (![0, 29848152952, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29848152952 : ℕ) : ℝ) ≤ ((![0, 29848152952, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((29843357938 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29843357938 ≤ (![0, 0, 29843357938] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29843357938 : ℕ) : ℝ) ≤ ((![0, 0, 29843357938] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85534235882 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85534235882 ≤ (![0, 85534235882, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85534235882 : ℕ) : ℝ) ≤ ((![0, 85534235882, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83900425454 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83900425454 ≤ (![0, 0, 83900425454] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83900425454 : ℕ) : ℝ) ≤ ((![0, 0, 83900425454] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30294238639 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30294238639 ≤ (![0, 30294238639, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30294238639 : ℕ) : ℝ) ≤ ((![0, 30294238639, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29918440055 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29918440055 ≤ (![0, 0, 29918440055] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29918440055 : ℕ) : ℝ) ≤ ((![0, 0, 29918440055] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2562591995 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2562591995 ≤ (![0, 2562591995, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2562591995 : ℕ) : ℝ) ≤ ((![0, 2562591995, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2532957755 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2532957755 ≤ (![0, 0, 2532957755] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2532957755 : ℕ) : ℝ) ≤ ((![0, 0, 2532957755] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((50087514 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        50087514 ≤ (![0, 50087514, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((50087514 : ℕ) : ℝ) ≤ ((![0, 50087514, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49684414 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49684414 ≤ (![0, 0, 49684414] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49684414 : ℕ) : ℝ) ≤ ((![0, 0, 49684414] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner1_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
