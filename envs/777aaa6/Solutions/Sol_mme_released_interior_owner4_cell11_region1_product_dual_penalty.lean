-- Prove2me | solution 1 for mme_released_interior_owner4_cell11_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:15:20.949629+00:00
-- url     : https://prove2.me/submissions/f88cdc62-c890-4a88-b8ba-2a0cb62dd990

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 4 11 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(37030263103 / 62500000000), (74060364543 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(23897402363875000000000000000000000 / 322682909556703826904804377037346297), (44464340875125000000000000000000000 / 322682909556703826904804377037346297), (23897295198625000000000000000000000 / 322682909556703826904804377037346297), (1 / 1), (1 / 1)], ![(1 / 1), (7534393319 / 50000000000), (3930755329227 / 1000000000000), (491343296271 / 125000000000), (150687620071 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![4, 3, 4, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-65428882089 / 125000000000), (-130858309891 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2602900371551 / 1000000000000), (-1981982597589 / 1000000000000), (-52058097119 / 20000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-378508938331 / 200000000000), (273766320629 / 200000000000), (684414661961 / 500000000000), (-94627316311 / 50000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-523431056711 / 1000000000000), (-523433239563 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-52058007431 / 20000000000), (-495495649397 / 250000000000), (-2602904855949 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-946272345827 / 500000000000), (684415801573 / 500000000000), (1368829323923 / 1000000000000), (-1892546326219 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1757504287193 / 1000000000000), (-627359719317 / 125000000000), (-1136584234003 / 1000000000000), (-568292165189 / 500000000000), (-250944139363 / 50000000000), (-351500861903 / 200000000000)] : List ℚ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-219688035899 / 125000000000), (-1003775550907 / 200000000000), (-568292117001 / 500000000000), (-1136584330377 / 1000000000000), (-5018882787259 / 1000000000000), (-878752154757 / 500000000000)] : List ℚ).getD
    ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 11) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 11 =>
        (splitWeight 4 11 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 11, ∏ i, weights i (c.val i) ≤ 1 := by
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
