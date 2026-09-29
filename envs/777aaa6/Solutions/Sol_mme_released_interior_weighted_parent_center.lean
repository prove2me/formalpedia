-- Prove2me | solution 1 for mme_released_interior_weighted_parent_center
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:59:08.329568+00:00
-- url     : https://prove2.me/submissions/1aae77c8-933a-4db8-a185-48e570cb09c3

import Theorems.Thm_mme_released_interior_aggregate_parent_counts
import Theorems.Thm_mme_released_interior_weighted_region_parent_mixture_exact

open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

/-- The released global word frequency is exactly the weighted mean of the
regional mixtures constructed from the released interior integer profiles. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (w : CompleteWord 3) :
    (∑ r : Fin 6, ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture (parent_total s) (regionalSize owner s)
        (splitCount owner s) (integerProfile owner s i) r
        ![((completeWordSplitEquiv 2 (by decide)) w).1,
          ((completeWordSplitEquiv 2 (by decide)) w).2]) =
    ((((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
        (denominator : ℝ) ^ 4 := by
  rw [mme_released_interior_aggregate_parent_counts owner s hi i w]
  simp_rw [mme_released_interior_weighted_region_parent_mixture_exact owner s hi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  ring


#print axioms solution
