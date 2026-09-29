-- Prove2me | solution 1 for mme_released_interior_owner0_cell26_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:43:54.888633+00:00
-- url     : https://prove2.me/submissions/0cf16110-303a-4727-b1fe-80d725d05d6b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(85579083713000000000000000000000000 / 8100695721576209647084424532243595031), (1195800733925000000000000000000000000 / 8100695721576209647084424532243595031), (1195896767150500000000000000000000000 / 8100695721576209647084424532243595031), (85599652501500000000000000000000000 / 8100695721576209647084424532243595031), (1 / 1)], ![(443799406519 / 1000000000000), (170047850909 / 200000000000), (8877413443 / 20000000000), (1 / 1), (1 / 1)], ![(20556670063 / 125000000000), (2491903458093 / 1000000000000), (311512940533 / 125000000000), (2570202599 / 15625000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4550264324383 / 1000000000000), (-956566959163 / 500000000000), (-59782925401 / 31250000000), (-1137506001237 / 250000000000), (0 / 1)], ![(-203095651439 / 250000000000), (-16223749317 / 100000000000), (-406111018961 / 500000000000), (0 / 1), (0 / 1)], ![(-1805128271749 / 1000000000000), (913046859441 / 1000000000000), (57070446419 / 62500000000), (-1804887467527 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2275132162191 / 500000000000), (-76525356733 / 40000000000), (-1913053612831 / 1000000000000), (-4550024004947 / 1000000000000), (0 / 1)], ![(-162476521151 / 200000000000), (-162237493169 / 1000000000000), (-812222037921 / 1000000000000), (0 / 1), (0 / 1)], ![(-451282067937 / 250000000000), (456523429721 / 500000000000), (182625428541 / 200000000000), (-902443733763 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-3244601536537 / 500000000000), (-4452980178939 / 1000000000000), (-2267165615681 / 500000000000), (-1162379317627 / 1000000000000), (-1811791848759 / 1000000000000), (-226473978481 / 125000000000), (-232475859091 / 200000000000), (-2267165580047 / 500000000000), (-4452980710809 / 1000000000000), (-6489203557361 / 1000000000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-6489203073073 / 1000000000000), (-2226490089469 / 500000000000), (-4534331231361 / 1000000000000), (-581189658813 / 500000000000), (-905895924379 / 500000000000), (-1811791827847 / 1000000000000), (-581189647727 / 500000000000), (-4534331160093 / 1000000000000), (-556622588851 / 125000000000), (-81115044467 / 12500000000)] : List ℚ).getD
    ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 26 4 c : ℝ) / 1000000000000) ≤
          (1565 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1565 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1565 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
