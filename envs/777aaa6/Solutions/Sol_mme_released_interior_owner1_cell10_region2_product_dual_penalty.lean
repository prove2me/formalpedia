-- Prove2me | solution 1 for mme_released_interior_owner1_cell10_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:25.259399+00:00
-- url     : https://prove2.me/submissions/4da55500-f4f0-4d7e-a818-c10e91482078

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 1 10 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(70673791058750000000000000000000000 / 314787859535242296359351086094551373), (70709219504250000000000000000000000 / 314787859535242296359351086094551373), (1 / 1), (1 / 1), (1 / 1)], ![(425236682311 / 500000000000), (850737360479 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (1 / 1), (119478624391 / 200000000000), (2017664284193 / 1000000000000), (60235206573 / 100000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, 3, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, -1, 1]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-298764830473 / 200000000000), (-1493322982583 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-80981092477 / 500000000000), (-40412955657 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-257589943283 / 500000000000), (350970273717 / 500000000000), (-15841036807 / 31250000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-373456038091 / 250000000000), (-746661491291 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-161962184953 / 1000000000000), (-161651822627 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (0 / 1), (-103035977313 / 200000000000), (140388109487 / 200000000000), (-506913177823 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 10) : ℤ :=
  ([2, 4, 4, 2] : List ℤ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-953535427557 / 1000000000000), (-2162699515141 / 1000000000000), (-2170154691781 / 1000000000000), (-476672310051 / 500000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 10) : ℚ :=
  ([(-238383856889 / 250000000000), (-108134975757 / 50000000000), (-108507734589 / 50000000000), (-953344620101 / 1000000000000)] : List ℚ).getD
    ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 10) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 1 10 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 10, ∏ i, weights i (c.val i) ≤ 1 := by
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
