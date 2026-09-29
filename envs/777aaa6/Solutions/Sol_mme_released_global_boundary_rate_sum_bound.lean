-- Prove2me | solution 1 for mme_released_global_boundary_rate_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T05:57:10.454164+00:00
-- url     : https://prove2.me/submissions/080aea7e-003e-4a1e-a89b-8a16e882dd8d

import Theorems.Thm_mme_released_global_owner0_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_uniform_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_uniform_boundary_volume_bound
import Theorems.Thm_mme_boundary_profile_volume_mass_entropy
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary

private def lowerNumerator (owner : Fin 6) (s : Fin 45) : ℕ :=
  (([[0, 49606893, 2486788621, 30163129815, 85574225979, 30069522158, 2518371893, 50007291, 0, 49279954, 0, 0, 0, 0, 0, 0, 49221705, 2462660104, 0, 0, 0, 0, 0, 2502501836, 29847986703, 0, 0, 0, 0, 29841607991, 85529917414, 0, 0, 0, 83916707382, 30295306029, 0, 0, 29916765458, 2562729051, 0, 2532605850, 50115012, 49741369, 0], [0, 49820906, 2487243242, 30161916128, 85578723810, 30067934123, 2518649441, 49990101, 0, 49245656, 0, 0, 0, 0, 0, 0, 49294690, 2462639231, 0, 0, 0, 0, 0, 2501614000, 29848152952, 0, 0, 0, 0, 29843357938, 85534235882, 0, 0, 0, 83900425454, 30294238639, 0, 0, 29918440055, 2562591995, 0, 2532957755, 50087514, 49684414, 0], [0, 49580151, 2486893764, 30162367654, 85581298089, 30068911217, 2518251968, 49951019, 0, 49419391, 0, 0, 0, 0, 0, 0, 49254970, 2460953691, 0, 0, 0, 0, 0, 2503308762, 29847430147, 0, 0, 0, 0, 29843034277, 85538626345, 0, 0, 0, 83898043062, 30296172800, 0, 0, 29916272233, 2563639178, 0, 2532488064, 50129517, 49757258, 0], [0, 49668638, 2487054614, 30163457323, 85576822698, 30067821815, 2517127730, 49831181, 0, 49330957, 0, 0, 0, 0, 0, 0, 49418204, 2462068005, 0, 0, 0, 0, 0, 2503068561, 29847084297, 0, 0, 0, 0, 29843979565, 85531596254, 0, 0, 0, 83903297232, 30295951027, 0, 0, 29916676812, 2563402632, 0, 2532342617, 49928473, 49653342, 0], [0, 49711049, 2486699145, 30158552205, 85573552848, 30073749198, 2518160978, 49964227, 0, 49385212, 0, 0, 0, 0, 0, 0, 49309756, 2461960971, 0, 0, 0, 0, 0, 2502955864, 29853036253, 0, 0, 0, 0, 29838417750, 85528069838, 0, 0, 0, 83902935981, 30289370898, 0, 0, 29921870728, 2563482978, 0, 2532716737, 50113951, 49674360, 0], [0, 49647854, 2487425428, 30161682257, 85580652520, 30068852496, 2518420453, 49984871, 0, 49396635, 0, 0, 0, 0, 0, 0, 49298498, 2462054477, 0, 0, 0, 0, 0, 2502852454, 29848185450, 0, 0, 0, 0, 29843118026, 85535730403, 0, 0, 0, 83899420204, 30295651400, 0, 0, 29918250959, 2562399822, 0, 2531327790, 49892168, 49891812, 0]] : List (List ℕ)).getD owner.val []).getD s.val 0

private def lower (j : Fin 270) : ℚ :=
  (lowerNumerator (component j).1 (component j).2 : ℚ) / 1000000000000

/-- The actual boundary witnesses from the outer extraction satisfy the
complete volume sum bound, with the extraction loss still explicit. -/
theorem solution
    (boundaryRate : Fin 270 → ℝ) (boundaryLoss : ℝ) (hloss : 0 ≤ boundaryLoss)
    (hzero : ∀ j, (0 < weight j ∨ coarseCounts (component j).1
      (shapeEquiv (component j).2) = 0) → boundaryRate j = 0)
    (hcert : ∀ j, ¬ 0 < weight j → 0 < coarseCounts (component j).1
      (shapeEquiv (component j).2) →
      ∃ (z : Fin 3) (B : Profile 3 (coarseCounts (component j).1 (shapeEquiv (component j).2))),
        ((shapeEquiv (component j).2).val z).val = 0 ∧
        (∀ i w, wordCounts (component j).1 i (shapeEquiv (component j).2) w = B.mu z i w) ∧
        boundaryRate j = (coarseCounts (component j).1 (shapeEquiv (component j).2) : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun w ↦ (B.count w : ℝ) /
            (coarseCounts (component j).1 (shapeEquiv (component j).2) : ℝ)) +
          ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - boundaryLoss) :
    (denominator : ℝ) ^ 5 * (337884154359 / 125000000000 : ℝ) -
      270 * boundaryLoss ≤ ∑ j, boundaryRate j := by
  have hb (owner : Fin 6) (s : Fin 45) (z : Fin 3)
      (hz : ((shape s).val z).val = 0) :
      (denominator : ℝ) ^ 5 * ((lowerNumerator owner s : ℝ) / 1000000000000) ≤
        massEntropy (fun w ↦ (wordCounts owner (z + 1) (shapeEquiv s) w : ℝ)) +
          (∑ w, (wordCounts owner (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by
    fin_cases owner
    · exact mme_released_global_owner0_uniform_boundary_volume_bound s z hz
    · exact mme_released_global_owner1_uniform_boundary_volume_bound s z hz
    · exact mme_released_global_owner2_uniform_boundary_volume_bound s z hz
    · exact mme_released_global_owner3_uniform_boundary_volume_bound s z hz
    · exact mme_released_global_owner4_uniform_boundary_volume_bound s z hz
    · exact mme_released_global_owner5_uniform_boundary_volume_bound s z hz
  have hn : ∀ j : Fin 270, (0 < weight j ∨
      alpha (component j).1 (component j).2 * denominator ^ 4 = 0) →
      lowerNumerator (component j).1 (component j).2 = 0 := by decide +kernel
  have hp (j : Fin 270) : (denominator : ℝ) ^ 5 * (lower j : ℝ) - boundaryLoss ≤ boundaryRate j := by
    by_cases hz : 0 < weight j ∨ coarseCounts (component j).1 (shapeEquiv (component j).2) = 0
    · have hn0 := hn j (by simpa only [coarseCounts, Equiv.symm_apply_apply] using hz)
      rw [hzero j hz]
      simp only [lower, hn0, Nat.cast_zero, zero_div, Rat.cast_zero, mul_zero, zero_sub]
      linarith
    · obtain ⟨z, B, hgrade, hmu, hrate⟩ := hcert j (fun h ↦ hz (Or.inl h))
        (Nat.pos_of_ne_zero (fun h ↦ hz (Or.inr h)))
      have hv := mme_boundary_profile_volume_mass_entropy B z
        (fun i w ↦ wordCounts (component j).1 i (shapeEquiv (component j).2) w) hmu
      simp only [Nat.cast_sum, Nat.cast_mul] at hv
      have h := hb (component j).1 (component j).2 z hgrade
      rw [← hv] at h
      simp only [lower, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
      rw [hrate]
      simp only [Nat.cast_sum, Nat.cast_mul]
      linarith
  have hsum : (∑ j : Fin 270, lower j) = (337884154359 / 125000000000 : ℚ) := by decide +kernel
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hp j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Rat.cast_sum, hsum] at hs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] using hs


#print axioms solution
