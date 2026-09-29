-- Prove2me | solution 1 for mme_released_global_owner2_uniform_boundary_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T04:56:52.679634+00:00
-- url     : https://prove2.me/submissions/2b5bbc48-353a-4dbc-9ae6-17ec68d48e41

import Theorems.Thm_mme_released_global_owner2_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell44_boundary_volume_bound

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

/-- A boundary cell retains its lower volume bound whichever zero coordinate
the extraction chooses. The bound is zero on nonboundary cells. -/
theorem solution (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49580151, 2486893764, 30162367654, 85581298089, 30068911217, 2518251968, 49951019, 0, 49419391, 0, 0, 0, 0, 0, 0, 49254970, 2460953691, 0, 0, 0, 0, 0, 2503308762, 29847430147, 0, 0, 0, 0, 29843034277, 85538626345, 0, 0, 0, 83898043062, 30296172800, 0, 0, 29916272233, 2563639178, 0, 2532488064, 50129517, 49757258, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 2 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 2 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
  fin_cases s
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell0_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 0).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49580151 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell1_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 1).val z).val = 0 →
        49580151 ≤ (![49580151, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49580151 : ℕ) : ℝ) ≤ ((![49580151, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2486893764 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell2_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 2).val z).val = 0 →
        2486893764 ≤ (![2486893764, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2486893764 : ℕ) : ℝ) ≤ ((![2486893764, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30162367654 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell3_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 3).val z).val = 0 →
        30162367654 ≤ (![30162367654, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30162367654 : ℕ) : ℝ) ≤ ((![30162367654, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85581298089 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell4_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 4).val z).val = 0 →
        85581298089 ≤ (![85581298089, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85581298089 : ℕ) : ℝ) ≤ ((![85581298089, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30068911217 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell5_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 5).val z).val = 0 →
        30068911217 ≤ (![30068911217, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30068911217 : ℕ) : ℝ) ≤ ((![30068911217, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2518251968 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell6_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 6).val z).val = 0 →
        2518251968 ≤ (![2518251968, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2518251968 : ℕ) : ℝ) ≤ ((![2518251968, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49951019 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell7_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 7).val z).val = 0 →
        49951019 ≤ (![49951019, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49951019 : ℕ) : ℝ) ≤ ((![49951019, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell8_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 8).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49419391 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell9_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 9).val z).val = 0 →
        49419391 ≤ (![0, 49419391, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49419391 : ℕ) : ℝ) ≤ ((![0, 49419391, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((49254970 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell16_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 16).val z).val = 0 →
        49254970 ≤ (![0, 0, 49254970] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49254970 : ℕ) : ℝ) ≤ ((![0, 0, 49254970] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2460953691 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell17_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 17).val z).val = 0 →
        2460953691 ≤ (![0, 2460953691, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2460953691 : ℕ) : ℝ) ≤ ((![0, 2460953691, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((2503308762 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell23_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 23).val z).val = 0 →
        2503308762 ≤ (![0, 0, 2503308762] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2503308762 : ℕ) : ℝ) ≤ ((![0, 0, 2503308762] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((29847430147 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell24_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 24).val z).val = 0 →
        29847430147 ≤ (![0, 29847430147, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29847430147 : ℕ) : ℝ) ≤ ((![0, 29847430147, 0] : Fin 3 → ℕ) z : ℝ) := by
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
  · change (denominator : ℝ) ^ 5 * (((29843034277 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell29_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 29).val z).val = 0 →
        29843034277 ≤ (![0, 0, 29843034277] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29843034277 : ℕ) : ℝ) ≤ ((![0, 0, 29843034277] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((85538626345 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell30_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 30).val z).val = 0 →
        85538626345 ≤ (![0, 85538626345, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((85538626345 : ℕ) : ℝ) ≤ ((![0, 85538626345, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 31).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 32).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 33).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((83898043062 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell34_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 34).val z).val = 0 →
        83898043062 ≤ (![0, 0, 83898043062] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((83898043062 : ℕ) : ℝ) ≤ ((![0, 0, 83898043062] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((30296172800 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell35_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 35).val z).val = 0 →
        30296172800 ≤ (![0, 30296172800, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((30296172800 : ℕ) : ℝ) ≤ ((![0, 30296172800, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 36).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · have hn : ∀ z : Fin 3, ((shape 37).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((29916272233 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell38_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 38).val z).val = 0 →
        29916272233 ≤ (![0, 0, 29916272233] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((29916272233 : ℕ) : ℝ) ≤ ((![0, 0, 29916272233] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((2563639178 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell39_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 39).val z).val = 0 →
        2563639178 ≤ (![0, 2563639178, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2563639178 : ℕ) : ℝ) ≤ ((![0, 2563639178, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · have hn : ∀ z : Fin 3, ((shape 40).val z).val ≠ 0 := by decide +kernel
    exact False.elim (hn z hz)
  · change (denominator : ℝ) ^ 5 * (((2532488064 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell41_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 41).val z).val = 0 →
        2532488064 ≤ (![0, 0, 2532488064] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((2532488064 : ℕ) : ℝ) ≤ ((![0, 0, 2532488064] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((50129517 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell42_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 42).val z).val = 0 →
        50129517 ≤ (![0, 50129517, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((50129517 : ℕ) : ℝ) ≤ ((![0, 50129517, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((49757258 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell43_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 43).val z).val = 0 →
        49757258 ≤ (![0, 0, 49757258] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((49757258 : ℕ) : ℝ) ≤ ((![0, 0, 49757258] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h
  · change (denominator : ℝ) ^ 5 * (((0 : ℕ) : ℝ) / 1000000000000) ≤ _
    have h := mme_released_global_owner2_cell44_boundary_volume_bound z hz
    have hn : ∀ z : Fin 3, ((shape 44).val z).val = 0 →
        0 ≤ (![0, 0, 0] : Fin 3 → ℕ) z := by decide +kernel
    have hr : ((0 : ℕ) : ℝ) ≤ ((![0, 0, 0] : Fin 3 → ℕ) z : ℝ) := by
      exact_mod_cast hn z hz
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (by norm_num)) (by positivity)).trans h


#print axioms solution
