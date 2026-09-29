-- Prove2me | solution 1 for mme_released_interior_owner0_cell21_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:37:18.741012+00:00
-- url     : https://prove2.me/submissions/c1162e57-f481-4fdf-bcf0-958899147001

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(418574973963000000000000000000000000 / 19976129485042647305673927422415406381), (776198072713000000000000000000000000 / 19976129485042647305673927422415406381), (418563393892000000000000000000000000 / 19976129485042647305673927422415406381), (1 / 1), (1 / 1)], ![(19481713113 / 500000000000), (2292425488859 / 1000000000000), (8556758315321 / 500000000000), (1146180488267 / 500000000000), (38963401203 / 1000000000000)], ![(1572552067 / 3906250000), (839533897481 / 1000000000000), (402562427149 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3865437290831 / 1000000000000), (-649577115603 / 200000000000), (-1932732478339 / 500000000000), (0 / 1), (0 / 1)], ![(-3245131861929 / 1000000000000), (414805211243 / 500000000000), (1419934298753 / 500000000000), (6481111567 / 7812500000), (-3245132504147 / 1000000000000)], ![(-909878014489 / 1000000000000), (-87454212551 / 500000000000), (-227476273911 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-386543729083 / 100000000000), (-1623942789007 / 500000000000), (-3865464956677 / 1000000000000), (0 / 1), (0 / 1)], ![(-405641482741 / 125000000000), (829610422487 / 1000000000000), (2839868597507 / 1000000000000), (829582280577 / 1000000000000), (-1622566252073 / 500000000000)], ![(-113734751811 / 125000000000), (-174908425101 / 1000000000000), (-909905095643 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1935473786929 / 1000000000000), (-802690860663 / 250000000000), (-8020447809649 / 1000000000000), (-1664090129697 / 500000000000), (-72865675701 / 125000000000), (-3328181303727 / 1000000000000), (-160410038271 / 20000000000), (-1605381475987 / 500000000000), (-1935474375703 / 1000000000000)] : List ℚ).getD
    ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-120967111683 / 62500000000), (-3210763442651 / 1000000000000), (-501277988103 / 62500000000), (-3328180259393 / 1000000000000), (-582925405607 / 1000000000000), (-1664090651863 / 500000000000), (-8020501913549 / 1000000000000), (-3210762951973 / 1000000000000), (-967737187851 / 500000000000)] : List ℚ).getD
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
        (splitWeight 0 21 5 c : ℝ) / 1000000000000) ≤
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
