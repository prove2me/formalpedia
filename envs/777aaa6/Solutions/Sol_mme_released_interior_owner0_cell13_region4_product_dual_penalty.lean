-- Prove2me | solution 1 for mme_released_interior_owner0_cell13_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:11.388742+00:00
-- url     : https://prove2.me/submissions/d3852d9e-47a1-44ea-84b1-11f1a419bcf1

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2729280120125000000000000000000000 / 122212307707162871203782357407548113), (2729317852000000000000000000000000 / 122212307707162871203782357407548113), (1 / 1), (1 / 1), (1 / 1)], ![(53318697803 / 1000000000000), (203307984113 / 100000000000), (3287866034889 / 250000000000), (2033140365799 / 1000000000000), (133296869 / 2500000000)], ![(273546874377 / 1000000000000), (143685658157 / 100000000000), (718437981719 / 500000000000), (273563111221 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 6, 0, 0, 0], ![5, -1, -3, -1, 5], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3801721877239 / 1000000000000), (-3801708052489 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-293146820627 / 100000000000), (354775903221 / 500000000000), (644133273459 / 250000000000), (709581575941 / 1000000000000), (-4580417613 / 1562500000)], ![(-1296282284687 / 1000000000000), (362457798059 / 1000000000000), (90617821761 / 250000000000), (-1296222929733 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1900860938619 / 500000000000), (-475213506561 / 125000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2931468206269 / 1000000000000), (709551806443 / 1000000000000), (2576533093837 / 1000000000000), (354790787971 / 500000000000), (-2931467272319 / 1000000000000)], ![(-648141142343 / 500000000000), (18122889903 / 50000000000), (72494257409 / 200000000000), (-324055732433 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-877678600113 / 200000000000), (-431358748179 / 500000000000), (-1364841251619 / 500000000000), (-4014735717183 / 500000000000), (-4014699593939 / 500000000000), (-682421239751 / 250000000000), (-862717160591 / 1000000000000), (-1097102190317 / 250000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-1097098250141 / 250000000000), (-862717496357 / 1000000000000), (-2729682503237 / 1000000000000), (-1605894286873 / 200000000000), (-8029399187877 / 1000000000000), (-2729684959003 / 1000000000000), (-86271716059 / 100000000000), (-4388408761267 / 1000000000000)] : List ℚ).getD
    ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 13 4 c : ℝ) / 1000000000000) ≤
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
