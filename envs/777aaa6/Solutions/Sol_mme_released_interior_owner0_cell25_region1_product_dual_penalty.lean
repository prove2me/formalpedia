-- Prove2me | solution 1 for mme_released_interior_owner0_cell25_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:26.071903+00:00
-- url     : https://prove2.me/submissions/1688d438-8dbe-4f77-b8a1-78be1f74e3fd

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(285446792703000000000000000000000000 / 17879027168615506144322927111402546009), (1366630293920000000000000000000000000 / 17879027168615506144322927111402546009), (1366629588622000000000000000000000000 / 17879027168615506144322927111402546009), (285446441403000000000000000000000000 / 17879027168615506144322927111402546009), (1 / 1)], ![(389982727439 / 1000000000000), (48747816097 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(52711880531 / 1000000000000), (391952577031 / 200000000000), (7196581571331 / 500000000000), (1959760843393 / 1000000000000), (26355936399 / 500000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4137327991919 / 1000000000000), (-642820072217 / 250000000000), (-1285640402477 / 500000000000), (-2068664611311 / 500000000000), (0 / 1)], ![(-470826414729 / 500000000000), (-941653338873 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1471457205911 / 500000000000), (336411744481 / 500000000000), (2666753312077 / 1000000000000), (8410280589 / 12500000000), (-117716582341 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2068663995959 / 500000000000), (-2571280288867 / 1000000000000), (-2571280804953 / 1000000000000), (-4137329222621 / 1000000000000), (0 / 1)], ![(-941652829457 / 1000000000000), (-117706667359 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2942914411821 / 1000000000000), (672823488963 / 1000000000000), (1333376656039 / 500000000000), (672822447121 / 1000000000000), (-735728639631 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 7, 5, 2, 2, 5, 7, 12] : List ℤ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-100273692257 / 12500000000), (-2203079441861 / 500000000000), (-2840110671213 / 1000000000000), (-423090157829 / 500000000000), (-423090161167 / 500000000000), (-1420055327433 / 500000000000), (-4406158563117 / 1000000000000), (-4010948487057 / 500000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8021895380559 / 1000000000000), (-4406158883721 / 1000000000000), (-710027667803 / 250000000000), (-846180315657 / 1000000000000), (-846180322333 / 1000000000000), (-568022130973 / 200000000000), (-1101539640779 / 250000000000), (-8021896974113 / 1000000000000)] : List ℚ).getD
    ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 0 25 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
