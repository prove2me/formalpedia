-- Prove2me | solution 1 for mme_released_interior_owner4_cell12_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:16:45.67365+00:00
-- url     : https://prove2.me/submissions/200b4bd1-bc54-4898-a241-04c7b2654ff5

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 4 12 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(194820697843 / 500000000000), (389640668547 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(141993629413500000000000000000000000 / 8955331408892075281172620183188896513), (686173120773500000000000000000000000 / 8955331408892075281172620183188896513), (686171857450000000000000000000000000 / 8955331408892075281172620183188896513), (141992664517000000000000000000000000 / 8955331408892075281172620183188896513), (1 / 1)], ![(26355262011 / 500000000000), (489913208643 / 250000000000), (14371565743297 / 1000000000000), (1959645064791 / 1000000000000), (6588815543 / 125000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![6, 4, 4, 6, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-471264230549 / 500000000000), (-471265163637 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-259013883047 / 62500000000), (-2568874363531 / 1000000000000), (-2568876204647 / 1000000000000), (-2072114462063 / 500000000000), (0 / 1)], ![(-4598343979 / 1562500000), (134553466467 / 200000000000), (1332625826663 / 500000000000), (672763367451 / 1000000000000), (-2942940140451 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-942528461097 / 1000000000000), (-942530327273 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4144222128751 / 1000000000000), (-256887436353 / 100000000000), (-1284438102323 / 500000000000), (-33153831393 / 8000000000), (0 / 1)], ![(-2942940146559 / 1000000000000), (42047958271 / 62500000000), (2665251653327 / 1000000000000), (168190841863 / 250000000000), (-58858802809 / 20000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 12) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-4413989088581 / 1000000000000), (-4014845364671 / 500000000000), (-846153037477 / 1000000000000), (-2838639457173 / 1000000000000), (-2838639199589 / 1000000000000), (-423076506209 / 500000000000), (-321187975929 / 40000000000), (-4413990052917 / 1000000000000)] : List ℚ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 12) : ℚ :=
  ([(-220699454429 / 50000000000), (-8029690729341 / 1000000000000), (-211538259369 / 250000000000), (-709659864293 / 250000000000), (-709659799897 / 250000000000), (-846153012417 / 1000000000000), (-501856212389 / 62500000000), (-1103497513229 / 250000000000)] : List ℚ).getD
    ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 12) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 12 =>
        (splitWeight 4 12 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 12, ∏ i, weights i (c.val i) ≤ 1 := by
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
