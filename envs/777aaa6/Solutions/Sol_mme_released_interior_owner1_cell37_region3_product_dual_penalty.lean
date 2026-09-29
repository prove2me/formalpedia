-- Prove2me | solution 1 for mme_released_interior_owner1_cell37_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:00.045298+00:00
-- url     : https://prove2.me/submissions/bc11180c-a91b-40f3-91c7-8572888ba0fb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (78957551578000000000000000000000000 / 3773757780419878889717512511773067151), (633374095117000000000000000000000000 / 1257919260139959629905837503924355717), (633374240198000000000000000000000000 / 1257919260139959629905837503924355717), (26319167646000000000000000000000000 / 1257919260139959629905837503924355717)], ![(146787843853 / 250000000000), (208941743597 / 200000000000), (117430322247 / 200000000000), (1 / 1), (1 / 1)], ![(74945271181 / 125000000000), (599562284291 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-12084112989 / 3125000000), (-343076509473 / 500000000000), (-137230557977 / 200000000000), (-3866916772507 / 1000000000000)], ![(-133118153163 / 250000000000), (43738107791 / 1000000000000), (-532472211013 / 1000000000000), (0 / 1), (0 / 1)], ![(-511555607727 / 1000000000000), (-255777708091 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3866916156479 / 1000000000000), (-137230603789 / 200000000000), (-171538197471 / 250000000000), (-1933458386253 / 500000000000)], ![(-532472612651 / 1000000000000), (2733631737 / 62500000000), (-133118052753 / 250000000000), (0 / 1), (0 / 1)], ![(-255777803863 / 500000000000), (-511555416181 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4910943783627 / 1000000000000), (-1730180837687 / 1000000000000), (-1153970327337 / 1000000000000), (-1153970289817 / 1000000000000), (-1730180818719 / 1000000000000), (-4910944992909 / 1000000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-2455471891813 / 500000000000), (-865090418843 / 500000000000), (-144246290917 / 125000000000), (-144246286227 / 125000000000), (-865090409359 / 500000000000), (-1227736248227 / 250000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 1 37 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
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
