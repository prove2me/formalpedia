-- Prove2me | solution 1 for mme_released_interior_owner0_shape19_region1_mode2_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:43:14.598235+00:00
-- url     : https://prove2.me/submissions/76dc2425-1d49-46d2-a26e-5cb3e01d6dcd

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
theorem solution :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 0 19 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 2)
    1 1 parentExponent compatibilityExponent (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 0 19 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc


#print axioms solution
