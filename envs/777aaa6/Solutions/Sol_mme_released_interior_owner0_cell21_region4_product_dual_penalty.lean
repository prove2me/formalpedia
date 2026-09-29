-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:17.942916+00:00
-- url     : https://prove2.me/submissions/7059c49d-2562-49ce-87bf-4f4ace2d7bdf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(82516204496400000000000000000000000 / 3966518724264192613126355632079549687), (161048778539400000000000000000000000 / 3966518724264192613126355632079549687), (82507947736000000000000000000000000 / 3966518724264192613126355632079549687), (1 / 1), (1 / 1)], ![(38984135481 / 1000000000000), (2311563310547 / 1000000000000), (16887778572451 / 1000000000000), (2311329680677 / 1000000000000), (4873003083 / 125000000000)], ![(411350354739 / 1000000000000), (161956698713 / 200000000000), (411309426547 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3872649401141 / 1000000000000), (-160196840097 / 50000000000), (-1936374734219 / 500000000000), (0 / 1), (0 / 1)], ![(-64892009963 / 20000000000), (104740506681 / 125000000000), (176661887433 / 62500000000), (837822978269 / 1000000000000), (-811150835193 / 250000000000)], ![(-888309982991 / 1000000000000), (-10549417947 / 50000000000), (-888409485101 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-193632470057 / 50000000000), (-3203936801939 / 1000000000000), (-3872749468437 / 1000000000000), (0 / 1), (0 / 1)], ![(-3244600498149 / 1000000000000), (837924053449 / 1000000000000), (2826590198929 / 1000000000000), (83782297827 / 100000000000), (-3244603340771 / 1000000000000)], ![(-88830998299 / 100000000000), (-210988358939 / 1000000000000), (-8884094851 / 10000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-3868937373 / 2000000000), (-129832591393 / 40000000000), (-8005562725623 / 1000000000000), (-813605559157 / 250000000000), (-588334961951 / 1000000000000), (-3254423803627 / 1000000000000), (-1000719931199 / 125000000000), (-3245813770927 / 1000000000000), (-1934469253313 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1934468686499 / 1000000000000), (-405726848103 / 125000000000), (-4002781362811 / 500000000000), (-3254422236627 / 1000000000000), (-11766699239 / 20000000000), (-1627211901813 / 500000000000), (-8005759449591 / 1000000000000), (-1622906885463 / 500000000000), (-30226082083 / 15625000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 0 21 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
