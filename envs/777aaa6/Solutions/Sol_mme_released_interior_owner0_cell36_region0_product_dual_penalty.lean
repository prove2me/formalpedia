-- Prove2me | solution 1 for mme_released_interior_owner0_cell36_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:10.786987+00:00
-- url     : https://prove2.me/submissions/54fb6088-cd33-404b-8712-3ccf1ab83378

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157428007436000000000000000000000000 / 7559676821897972481316969568662035647), (3809120162949000000000000000000000000 / 7559676821897972481316969568662035647), (3809118615912000000000000000000000000 / 7559676821897972481316969568662035647), (157427812471000000000000000000000000 / 7559676821897972481316969568662035647)], ![(599087095301 / 1000000000000), (149771708381 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(117272182277 / 200000000000), (209156152651 / 200000000000), (36647547099 / 62500000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3871615461713 / 1000000000000), (-685430206741 / 1000000000000), (-342715306441 / 500000000000), (-3871616700153 / 1000000000000)], ![(-512348290267 / 1000000000000), (-512348727227 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-133454947313 / 250000000000), (11190937079 / 250000000000), (-133455014593 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-241975966357 / 62500000000), (-34271510337 / 50000000000), (-685430612881 / 1000000000000), (-483952087519 / 125000000000)], ![(-256174145133 / 500000000000), (-256174363613 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533819789251 / 1000000000000), (44763748317 / 1000000000000), (-533820058371 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-614723030907 / 125000000000), (-1731598555377 / 1000000000000), (-1153015185651 / 1000000000000), (-72063447177 / 62500000000), (-865799564681 / 500000000000), (-49177847797 / 10000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-983556849451 / 200000000000), (-108224909711 / 62500000000), (-23060303713 / 20000000000), (-1153015154831 / 1000000000000), (-1731599129361 / 1000000000000), (-4917784779699 / 1000000000000)] : List ℚ).getD
    ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 36 0 c : ℝ) / 1000000000000) ≤
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
