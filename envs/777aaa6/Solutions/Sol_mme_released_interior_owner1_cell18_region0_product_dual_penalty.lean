-- Prove2me | solution 1 for mme_released_interior_owner1_cell18_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T13:17:15.152291+00:00
-- url     : https://prove2.me/submissions/b7479afb-56f8-4eee-809b-5be8de4493e7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 1 18 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(573344796851000000000000000000000000 / 7738444550809736804858165538121231291), (1068725591807000000000000000000000000 / 7738444550809736804858165538121231291), (573340942526000000000000000000000000 / 7738444550809736804858165538121231291), (1 / 1), (1 / 1)], ![(592729074687 / 1000000000000), (592727111309 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (151072213833 / 1000000000000), (490327841341 / 125000000000), (784521808033 / 200000000000), (151072038777 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1301234354257 / 500000000000), (-989866901023 / 500000000000), (-1301237715531 / 500000000000), (0 / 1), (0 / 1)], ![(-523017856749 / 1000000000000), (-65377646149 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-944998659591 / 500000000000), (34169012351 / 25000000000), (683378501939 / 500000000000), (-94499923897 / 50000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2602468708513 / 1000000000000), (-395946760409 / 200000000000), (-2602475431061 / 1000000000000), (0 / 1), (0 / 1)], ![(-130754464187 / 250000000000), (-523021169191 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1889997319181 / 1000000000000), (1366760494041 / 1000000000000), (1366757003879 / 1000000000000), (-1889998477939 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 18) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-879366436913 / 500000000000), (-1253871260823 / 250000000000), (-567997238599 / 500000000000), (-567997327457 / 500000000000), (-200619756779 / 40000000000), (-219841599221 / 125000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 18) : ℚ :=
  ([(-54960402307 / 31250000000), (-5015485043291 / 1000000000000), (-1135994477197 / 1000000000000), (-1135994654913 / 1000000000000), (-2507746959737 / 500000000000), (-1758732793767 / 1000000000000)] : List ℚ).getD
    ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 18) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 18 =>
        (splitWeight 1 18 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 18, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
