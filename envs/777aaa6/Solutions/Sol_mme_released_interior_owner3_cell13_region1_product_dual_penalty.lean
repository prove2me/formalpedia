-- Prove2me | solution 1 for mme_released_interior_owner3_cell13_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:05:44.75503+00:00
-- url     : https://prove2.me/submissions/56d6b2ea-88be-4995-8a11-ff2976925aaf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 3 13 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(48934319109 / 125000000000), (391475576341 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(5307059097 / 100000000000), (501182421287 / 250000000000), (13599289334027 / 1000000000000), (80189601259 / 40000000000), (13267652343 / 250000000000)], ![(21279596619000000000000000000000000 / 1364494271616751815349303998026441431), (108880149044000000000000000000000000 / 1364494271616751815349303998026441431), (1415445658296000000000000000000000000 / 17738425531017773599540951974343738603), (276636658199000000000000000000000000 / 17738425531017773599540951974343738603), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-468917382357 / 500000000000), (-937832150323 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-587226469307 / 200000000000), (347754615647 / 500000000000), (104400701461 / 40000000000), (695514392239 / 1000000000000), (-2936131999789 / 1000000000000)], ![(-832158086713 / 200000000000), (-2528291414759 / 1000000000000), (-2528288786097 / 1000000000000), (-4160783557547 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-937834764713 / 1000000000000), (-468916075161 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1468066173267 / 500000000000), (139101846259 / 200000000000), (1305008768263 / 500000000000), (8693929903 / 12500000000), (-734032999947 / 250000000000)], ![(-1040197608391 / 250000000000), (-1264145707379 / 500000000000), (-158018049131 / 62500000000), (-2080391778773 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-4017378598271 / 500000000000), (-4403108191659 / 1000000000000), (-2770611787233 / 1000000000000), (-214026507139 / 250000000000), (-214026503571 / 250000000000), (-2770611705123 / 1000000000000), (-220155454549 / 50000000000), (-4017374027349 / 500000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8034757196541 / 1000000000000), (-2201554095829 / 500000000000), (-86581618351 / 31250000000), (-171221205711 / 200000000000), (-856106014283 / 1000000000000), (-1385305852561 / 500000000000), (-4403109090979 / 1000000000000), (-8034748054697 / 1000000000000)] : List ℚ).getD
    ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 13 1 c : ℝ) / 1000000000000) ≤
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
