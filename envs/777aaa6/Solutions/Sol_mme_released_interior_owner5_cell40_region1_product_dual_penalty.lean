-- Prove2me | solution 1 for mme_released_interior_owner5_cell40_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:24:08.321216+00:00
-- url     : https://prove2.me/submissions/6ea29703-8f56-4ae6-9889-17458d791a17

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 5 40 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (1 / 1), (30463120123 / 50000000000), (1959344681629 / 1000000000000), (609206331671 / 1000000000000)], ![(21322104647 / 25000000000), (852883649239 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(142147106013000000000000000000000000 / 622821221413641053569959246753530443), (142155303715000000000000000000000000 / 622821221413641053569959246753530443), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 0, 1, 0, 1], ![1, 1, 0, 0, 0], ![3, 3, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-247753114877 / 500000000000), (168152517807 / 250000000000), (-123899566149 / 250000000000)], ![(-159131513417 / 1000000000000), (-1273057141 / 8000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-738698517189 / 500000000000), (-1477339365489 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (0 / 1), (-495506229753 / 1000000000000), (672610071229 / 1000000000000), (-99119652919 / 200000000000)], ![(-19891439177 / 125000000000), (-4972879457 / 31250000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1477397034377 / 1000000000000), (-92333710343 / 62500000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 40) : ℤ :=
  ([4, 2, 2, 4] : List ℤ).getD
    ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-266515851549 / 125000000000), (-481959552887 / 500000000000), (-481930403837 / 500000000000), (-532994434467 / 250000000000)] : List ℚ).getD
    ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 40) : ℚ :=
  ([(-2132126812391 / 1000000000000), (-963919105773 / 1000000000000), (-963860807673 / 1000000000000), (-2131977737867 / 1000000000000)] : List ℚ).getD
    ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 40) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 40 =>
        (splitWeight 5 40 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 40, ∏ i, weights i (c.val i) ≤ 1 := by
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
