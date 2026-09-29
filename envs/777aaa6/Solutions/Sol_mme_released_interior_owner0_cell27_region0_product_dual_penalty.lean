-- Prove2me | solution 1 for mme_released_interior_owner0_cell27_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:56.402989+00:00
-- url     : https://prove2.me/submissions/007b3b1a-9c31-4c51-8e5e-25cd5606a974

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(165628302656000000000000000000000000 / 16192710926337705989956537352697031529), (2476280323233000000000000000000000000 / 16192710926337705989956537352697031529), (2476381148643000000000000000000000000 / 16192710926337705989956537352697031529), (165647612055000000000000000000000000 / 16192710926337705989956537352697031529), (1 / 1)], ![(1703310097 / 10000000000), (2406339941639 / 1000000000000), (2406437076271 / 1000000000000), (85176339319 / 500000000000), (1 / 1)], ![(221927217239 / 500000000000), (84966758151 / 100000000000), (443890703611 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4582570340041 / 1000000000000), (-1877803633583 / 1000000000000), (-375552583587 / 200000000000), (-4582453764111 / 1000000000000), (0 / 1)], ![(-1770011619223 / 1000000000000), (439053448349 / 500000000000), (439073631007 / 500000000000), (-1769884410679 / 1000000000000), (0 / 1)], ![(-40612931029 / 50000000000), (-162910086567 / 1000000000000), (-203044227473 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-114564258501 / 25000000000), (-938901816791 / 500000000000), (-938881458967 / 500000000000), (-458245376411 / 100000000000), (0 / 1)], ![(-885005809611 / 500000000000), (878106896699 / 1000000000000), (175629452403 / 200000000000), (-884942205339 / 500000000000), (0 / 1)], ![(-812258620579 / 1000000000000), (-81455043283 / 500000000000), (-812176909891 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-45205802821 / 10000000000), (-6486470400581 / 1000000000000), (-1811342376101 / 1000000000000), (-23254105477 / 20000000000), (-892741463593 / 200000000000), (-4463712080043 / 1000000000000), (-145338115609 / 125000000000), (-181134300549 / 100000000000), (-6486481018661 / 1000000000000), (-565073220457 / 125000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4520580282099 / 1000000000000), (-324323520029 / 50000000000), (-18113423761 / 10000000000), (-1162705273849 / 1000000000000), (-1115926829491 / 250000000000), (-2231856040021 / 500000000000), (-1162704924871 / 1000000000000), (-1811343005489 / 1000000000000), (-324324050933 / 50000000000), (-904117152731 / 200000000000)] : List ℚ).getD
    ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 0 27 0 c : ℝ) / 1000000000000) ≤
          (1649 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1649 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1649 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
