-- Prove2me | solution 1 for mme_released_interior_owner2_cell27_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:30.577981+00:00
-- url     : https://prove2.me/submissions/9bbc3ef8-042a-47cc-a7ce-7050c8476170

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 2 27 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(88251002481 / 500000000000), (1172584095221 / 500000000000), (1172639372607 / 500000000000), (176528331351 / 1000000000000), (1 / 1)], ![(42254040352000000000000000000000000 / 3964829808943341964282418757304004811), (613280355511000000000000000000000000 / 3964829808943341964282418757304004811), (613309559763250000000000000000000000 / 3964829808943341964282418757304004811), (42259725056000000000000000000000000 / 3964829808943341964282418757304004811), (1 / 1)], ![(22250090629 / 50000000000), (864626524701 / 1000000000000), (445043994041 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-433605760779 / 250000000000), (852357122329 / 1000000000000), (852404262729 / 1000000000000), (-1734273897921 / 1000000000000), (0 / 1)], ![(-4541518230941 / 1000000000000), (-373279205697 / 200000000000), (-1866348409877 / 1000000000000), (-141918240739 / 31250000000), (0 / 1)], ![(-809676923611 / 1000000000000), (-145457628639 / 1000000000000), (-80958213869 / 100000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-346884608623 / 200000000000), (85235712233 / 100000000000), (85240426273 / 100000000000), (-5419605931 / 3125000000), (0 / 1)], ![(-227075911547 / 50000000000), (-466599007121 / 250000000000), (-466587102469 / 250000000000), (-4541383703647 / 1000000000000), (0 / 1)], ![(-80967692361 / 100000000000), (-72728814319 / 500000000000), (-809582138689 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-180031560313 / 40000000000), (-6407053872587 / 1000000000000), (-113958311349 / 62500000000), (-579761770129 / 500000000000), (-4412262607861 / 1000000000000), (-2206134665707 / 500000000000), (-579761531607 / 500000000000), (-911666503747 / 500000000000), (-1601767128141 / 250000000000), (-2250398193713 / 500000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-281299312989 / 62500000000), (-3203526936293 / 500000000000), (-1823332981583 / 1000000000000), (-1159523540257 / 1000000000000), (-220613130393 / 50000000000), (-4412269331413 / 1000000000000), (-1159523063213 / 1000000000000), (-1823333007493 / 1000000000000), (-6407068512563 / 1000000000000), (-180031855497 / 40000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 27 1 c : ℝ) / 1000000000000) ≤
          (440 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (440 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((440 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
