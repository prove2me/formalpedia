-- Prove2me | solution 1 for mme_released_interior_owner2_cell31_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:36.793973+00:00
-- url     : https://prove2.me/submissions/51dc789a-2928-4a67-bc26-a49d289d4814

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 2 31 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53326830887 / 1000000000000), (50853918689 / 25000000000), (13133536162859 / 1000000000000), (1017176497821 / 500000000000), (53327160531 / 1000000000000)], ![(353623341000000000000000000000000 / 15849953986529028159337046825676383), (353640274000000000000000000000000 / 15849953986529028159337046825676383), (1 / 1), (1 / 1), (1 / 1)], ![(272870495673 / 1000000000000), (1439896229053 / 1000000000000), (35999130893 / 25000000000), (136455099557 / 500000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![6, 6, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2931315680719 / 1000000000000), (355040679177 / 500000000000), (2575168971389 / 1000000000000), (355088915041 / 500000000000), (-2931309499159 / 1000000000000)], ![(-3802689538043 / 1000000000000), (-3802641654907 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1298757971173 / 1000000000000), (364571047833 / 1000000000000), (72923794287 / 200000000000), (-259722495777 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1465657840359 / 500000000000), (142016271671 / 200000000000), (257516897139 / 100000000000), (710177830083 / 1000000000000), (-1465654749579 / 500000000000)], ![(-1901344769021 / 500000000000), (-1901320827453 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-324689492793 / 250000000000), (182285523917 / 500000000000), (91154742859 / 250000000000), (-324653119721 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([7, 2, 4, 12, 12, 4, 2, 7] : List ℤ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4391220658561 / 1000000000000), (-862901595217 / 1000000000000), (-1363970330067 / 500000000000), (-803275700809 / 100000000000), (-2008142453967 / 250000000000), (-545588265023 / 200000000000), (-172580327137 / 200000000000), (-4391221796011 / 1000000000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-6861282279 / 1562500000), (-53931349701 / 62500000000), (-2727940660133 / 1000000000000), (-8032757008089 / 1000000000000), (-8032569815867 / 1000000000000), (-1363970662557 / 500000000000), (-215725408921 / 250000000000), (-439122179601 / 100000000000)] : List ℚ).getD
    ((seed 2 31).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 2 31 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
