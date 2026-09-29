-- Prove2me | solution 1 for mme_released_interior_owner4_cell27_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:18:09.054969+00:00
-- url     : https://prove2.me/submissions/1fa446e5-4157-4590-b9b7-3c1106cd0e33

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 4 27 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(21397366649 / 125000000000), (1196914289727 / 500000000000), (2393665410501 / 1000000000000), (85572254623 / 500000000000), (1 / 1)], ![(82442993930500000000000000000000000 / 8092276228734104835221086155766430783), (1243205968223500000000000000000000000 / 8092276228734104835221086155766430783), (1243121505969000000000000000000000000 / 8092276228734104835221086155766430783), (82425860666000000000000000000000000 / 8092276228734104835221086155766430783), (1 / 1)], ![(27758651559 / 62500000000), (850327672091 / 1000000000000), (88815595561 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-220630734579 / 125000000000), (872894000333 / 1000000000000), (109103229459 / 125000000000), (-441311749013 / 250000000000), (0 / 1)], ![(-4586558261891 / 1000000000000), (-1873216553437 / 1000000000000), (-468321123703 / 250000000000), (-2293383051511 / 500000000000), (0 / 1)], ![(-792596677 / 976562500), (-32426701441 / 200000000000), (-202938776571 / 250000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1765045876631 / 1000000000000), (436447000167 / 500000000000), (872825835673 / 1000000000000), (-1765246996051 / 1000000000000), (0 / 1)], ![(-458655826189 / 100000000000), (-468304138359 / 250000000000), (-1873284494811 / 1000000000000), (-4586766103021 / 1000000000000), (0 / 1)], ![(-811618997247 / 1000000000000), (-40533376801 / 250000000000), (-811755106283 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1297112866041 / 200000000000), (-4529435620741 / 1000000000000), (-2226871675631 / 500000000000), (-232532139187 / 200000000000), (-452888807969 / 250000000000), (-1811555228877 / 1000000000000), (-116266047349 / 100000000000), (-4453746269547 / 1000000000000), (-2264719588479 / 500000000000), (-6485571043663 / 1000000000000)] : List ℚ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-1621391082551 / 250000000000), (-226471781037 / 50000000000), (-4453743351261 / 1000000000000), (-581330347967 / 500000000000), (-2898488371 / 1600000000), (-452888807219 / 250000000000), (-1162660473489 / 1000000000000), (-2226873134773 / 500000000000), (-4529439176957 / 1000000000000), (-3242785521831 / 500000000000)] : List ℚ).getD
    ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 27 1 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1592 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1592 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
