-- Prove2me | solution 1 for mme_released_interior_owner3_cell26_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:22.821301+00:00
-- url     : https://prove2.me/submissions/fe042364-65ad-4872-b9dd-2f575fcb5c8f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 3 26 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(35292531533 / 200000000000), (2344071121963 / 1000000000000), (2344182017751 / 1000000000000), (176489310903 / 1000000000000), (1 / 1)], ![(444756226461 / 1000000000000), (27012122561 / 31250000000), (444798572049 / 1000000000000), (1 / 1), (1 / 1)], ![(168497308070000000000000000000000000 / 15881224378513681513493122539761480609), (2458910786127000000000000000000000000 / 15881224378513681513493122539761480609), (2459028488682000000000000000000000000 / 15881224378513681513493122539761480609), (168519847307000000000000000000000000 / 15881224378513681513493122539761480609), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1734645996297 / 1000000000000), (212972303347 / 250000000000), (212984130331 / 250000000000), (-1734494965899 / 1000000000000), (0 / 1)], ![(-405114476311 / 500000000000), (-145733627201 / 1000000000000), (-810133746373 / 1000000000000), (0 / 1), (0 / 1)], ![(-1136493264983 / 250000000000), (-1865419072743 / 1000000000000), (-1865371206127 / 1000000000000), (-4545839302723 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-216830749537 / 125000000000), (851889213389 / 1000000000000), (34077460853 / 40000000000), (-867247482949 / 500000000000), (0 / 1)], ![(-810228952621 / 1000000000000), (-91083517 / 625000000), (-202533436593 / 250000000000), (0 / 1), (0 / 1)], ![(-4545973059931 / 1000000000000), (-932709536371 / 500000000000), (-932685603063 / 500000000000), (-2272919651361 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2253121098541 / 500000000000), (-3206077138831 / 500000000000), (-911689986467 / 500000000000), (-231857832731 / 200000000000), (-1103007197563 / 250000000000), (-2206018363101 / 500000000000), (-1159288606349 / 1000000000000), (-911690002311 / 500000000000), (-3206085789917 / 500000000000), (-2253125466049 / 500000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4506242197081 / 1000000000000), (-6412154277661 / 1000000000000), (-1823379972933 / 1000000000000), (-579644581827 / 500000000000), (-4412028790251 / 1000000000000), (-4412036726201 / 1000000000000), (-289822151587 / 250000000000), (-1823380004621 / 1000000000000), (-6412171579833 / 1000000000000), (-4506250932097 / 1000000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 3 26 1 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (428 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((428 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
