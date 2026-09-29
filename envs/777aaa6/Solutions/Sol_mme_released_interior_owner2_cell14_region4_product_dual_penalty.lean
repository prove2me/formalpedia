-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:19:07.214856+00:00
-- url     : https://prove2.me/submissions/e9153511-0dc3-4477-9f1c-129000cfbdee

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 2 14 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(298396044867 / 500000000000), (74598984913 / 125000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (19354177791500000000000000000000000 / 954019669490277843845219584887909357), (160596655732500000000000000000000000 / 318006556496759281281739861629303119), (481789783469750000000000000000000000 / 954019669490277843845219584887909357), (19354161603250000000000000000000000 / 954019669490277843845219584887909357)], ![(581199580639 / 1000000000000), (1054454178207 / 1000000000000), (581199153281 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-64523310581 / 125000000000), (-2064747349 / 4000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-1948887993221 / 500000000000), (-68317602277 / 100000000000), (-341588202057 / 500000000000), (-243611051429 / 62500000000)], ![(-54266106883 / 100000000000), (53023266419 / 1000000000000), (-271330902067 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-516186484647 / 1000000000000), (-516186837249 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3897775986441 / 1000000000000), (-683176022769 / 1000000000000), (-683176404113 / 1000000000000), (-3897776822863 / 1000000000000)], ![(-542661068829 / 1000000000000), (2651163321 / 50000000000), (-542661804133 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2478312313889 / 500000000000), (-6804782467 / 3906250000), (-573169796801 / 500000000000), (-57316981117 / 50000000000), (-1742024310193 / 1000000000000), (-247831218819 / 50000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4956624627777 / 1000000000000), (-1742024311551 / 1000000000000), (-1146339593601 / 1000000000000), (-1146339622339 / 1000000000000), (-108876519387 / 62500000000), (-4956624376379 / 1000000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 2 14 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
