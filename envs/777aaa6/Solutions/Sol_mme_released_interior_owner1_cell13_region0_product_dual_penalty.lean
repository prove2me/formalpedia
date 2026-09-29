-- Prove2me | solution 1 for mme_released_interior_owner1_cell13_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:32.62321+00:00
-- url     : https://prove2.me/submissions/ff71779e-fe7e-40c7-86b2-0f2ed46e3b0e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(28087852815500000000000000000000000 / 1255567003154075608376080582868810047), (196614721659500000000000000000000000 / 8788969022078529258632564080081670329), (1 / 1), (1 / 1), (1 / 1)], ![(26652704249 / 500000000000), (508683766991 / 250000000000), (6582684538501 / 500000000000), (508682877041 / 250000000000), (2665270763 / 50000000000)], ![(137228312517 / 500000000000), (1432731410309 / 1000000000000), (716364699717 / 500000000000), (137228774781 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3800005346147 / 1000000000000), (-1900003303873 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2931717480201 / 1000000000000), (355182811343 / 500000000000), (644397456817 / 250000000000), (710363873169 / 1000000000000), (-2931717353347 / 1000000000000)], ![(-1292962044967 / 1000000000000), (359582699533 / 1000000000000), (179790648003 / 500000000000), (-323239669099 / 250000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1900002673073 / 500000000000), (-760001321549 / 200000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-14658587401 / 5000000000), (710365622687 / 1000000000000), (2577589827269 / 1000000000000), (71036387317 / 100000000000), (-1465858676673 / 500000000000)], ![(-646481022483 / 500000000000), (179791349767 / 500000000000), (359581296007 / 1000000000000), (-258591735279 / 200000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 4, 2, 7, 7, 2, 4, 12] : List ℤ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-1003085592937 / 125000000000), (-2730058773437 / 1000000000000), (-862834222873 / 1000000000000), (-4382598399861 / 1000000000000), (-547825597441 / 125000000000), (-431417040473 / 500000000000), (-341257461131 / 125000000000), (-4012341381781 / 500000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-1604936948699 / 200000000000), (-682514693359 / 250000000000), (-107854277859 / 125000000000), (-219129919993 / 50000000000), (-4382604779527 / 1000000000000), (-172566816189 / 200000000000), (-2730059689047 / 1000000000000), (-8024682763561 / 1000000000000)] : List ℚ).getD
    ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 1 13 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
