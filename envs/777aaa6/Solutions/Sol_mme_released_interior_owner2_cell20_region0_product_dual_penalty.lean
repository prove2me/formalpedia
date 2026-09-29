-- Prove2me | solution 1 for mme_released_interior_owner2_cell20_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:11.705384+00:00
-- url     : https://prove2.me/submissions/d0899bc3-823c-4ef0-aee5-c1140ecd136e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 2 20 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(13896358663 / 31250000000), (54012258437 / 62500000000), (222317460077 / 500000000000), (1 / 1), (1 / 1)], ![(84429959768500000000000000000000000 / 7957761875285385623691417529555084591), (1224375659577000000000000000000000000 / 7957761875285385623691417529555084591), (1224308832647000000000000000000000000 / 7957761875285385623691417529555084591), (84416074938500000000000000000000000 / 7957761875285385623691417529555084591), (1 / 1)], ![(34995441181 / 200000000000), (590077295279 / 250000000000), (2360180368581 / 1000000000000), (174948379407 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-25324766783 / 31250000000), (-18244440981 / 125000000000), (-10131271721 / 12500000000), (0 / 1), (0 / 1)], ![(-2272990377841 / 500000000000), (-1871716740453 / 1000000000000), (-467942830589 / 250000000000), (-4546145223033 / 1000000000000), (0 / 1)], ![(-871549782757 / 500000000000), (214698154851 / 250000000000), (858738043481 / 1000000000000), (-174326432339 / 100000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-162078507411 / 200000000000), (-145955527847 / 1000000000000), (-810501737679 / 1000000000000), (0 / 1), (0 / 1)], ![(-4545980755681 / 1000000000000), (-467929185113 / 250000000000), (-374354264471 / 200000000000), (-568268152879 / 125000000000), (0 / 1)], ![(-1743099565513 / 1000000000000), (171758523881 / 200000000000), (429369021741 / 500000000000), (-1743264323389 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6421548371007 / 1000000000000), (-2249863389053 / 500000000000), (-2213608703503 / 500000000000), (-579502244463 / 500000000000), (-1823152788687 / 1000000000000), (-911576372949 / 500000000000), (-1159004494917 / 1000000000000), (-2213608214831 / 500000000000), (-4499727470149 / 1000000000000), (-6421548085669 / 1000000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-3210774185503 / 500000000000), (-899945355621 / 200000000000), (-885443481401 / 200000000000), (-46360179557 / 40000000000), (-911576394343 / 500000000000), (-1823152745897 / 1000000000000), (-289751123729 / 250000000000), (-4427216429661 / 1000000000000), (-1124931867537 / 250000000000), (-1605387021417 / 250000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 2 20 0 c : ℝ) / 1000000000000) ≤
          (400 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (400 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((400 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
