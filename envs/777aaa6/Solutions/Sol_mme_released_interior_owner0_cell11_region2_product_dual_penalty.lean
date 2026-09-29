-- Prove2me | solution 1 for mme_released_interior_owner0_cell11_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:06.306623+00:00
-- url     : https://prove2.me/submissions/233384ab-7744-46bb-9418-7e5a02e66adb

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(11848801554100000000000000000000000 / 154897274960423538430421193990705259), (11848776794200000000000000000000000 / 154897274960423538430421193990705259), (1 / 1), (1 / 1), (1 / 1)], ![(286756232839 / 500000000000), (533578541121 / 500000000000), (143377525469 / 250000000000), (1 / 1), (1 / 1)], ![(1 / 1), (150660914037 / 1000000000000), (1965668214743 / 500000000000), (245707981063 / 62500000000), (150660910089 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![4, 4, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 3, -1, -1, 3]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2570535427227 / 1000000000000), (-2570537516883 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-277987803253 / 500000000000), (812477251 / 12500000000), (-277989864069 / 500000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-946361784859 / 500000000000), (1368979426467 / 1000000000000), (42780537663 / 31250000000), (-946361797961 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1285267713613 / 500000000000), (-1285268758441 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-111195121301 / 200000000000), (64998180081 / 1000000000000), (-555979728137 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1892723569717 / 1000000000000), (342244856617 / 250000000000), (1368977205217 / 1000000000000), (-1892723595921 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 11) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-1254808657419 / 250000000000), (-1136560041931 / 1000000000000), (-878767864447 / 500000000000), (-878767959087 / 500000000000), (-568279955167 / 500000000000), (-1003848162961 / 200000000000)] : List ℚ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 11) : ℚ :=
  ([(-200769385187 / 40000000000), (-113656004193 / 100000000000), (-1757535728893 / 1000000000000), (-1757535918173 / 1000000000000), (-1136559910333 / 1000000000000), (-1254810203701 / 250000000000)] : List ℚ).getD
    ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 11 2 c : ℝ) / 1000000000000) ≤
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
