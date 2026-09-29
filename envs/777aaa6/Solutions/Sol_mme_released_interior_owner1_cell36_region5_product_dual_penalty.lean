-- Prove2me | solution 1 for mme_released_interior_owner1_cell36_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:46.616529+00:00
-- url     : https://prove2.me/submissions/53b07f19-815c-430c-9fee-e5d7c5cc205f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157931569603000000000000000000000000 / 7549757377946702481469372631508121453), (3799233786106000000000000000000000000 / 7549757377946702481469372631508121453), (3799236963823000000000000000000000000 / 7549757377946702481469372631508121453), (157931595221000000000000000000000000 / 7549757377946702481469372631508121453)], ![(600035438233 / 1000000000000), (75004489421 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(146792900867 / 250000000000), (1044302893513 / 1000000000000), (587172534553 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-966777217731 / 250000000000), (-42919751013 / 62500000000), (-343357589899 / 500000000000), (-1933554354357 / 500000000000)], ![(-510766561789 / 1000000000000), (-510765766611 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-133109540517 / 250000000000), (43349575267 / 1000000000000), (-266218288179 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3867108870923 / 1000000000000), (-686716016207 / 1000000000000), (-686715179797 / 1000000000000), (-3867108708713 / 1000000000000)], ![(-127691640447 / 250000000000), (-51076576661 / 100000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-532438162067 / 1000000000000), (10837393817 / 250000000000), (-532436576357 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-2455155606917 / 500000000000), (-23082644151 / 20000000000), (-864959577177 / 500000000000), (-1729919108477 / 1000000000000), (-14426652079 / 12500000000), (-4910313432639 / 1000000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4910311213833 / 1000000000000), (-1154132207549 / 1000000000000), (-1729919154353 / 1000000000000), (-432479777119 / 250000000000), (-1154132166319 / 1000000000000), (-2455156716319 / 500000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 1 36 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
