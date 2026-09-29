-- Prove2me | solution 1 for mme_released_interior_owner0_shape19_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:30:57.798117+00:00
-- url     : https://prove2.me/submissions/44ce652b-81ea-47c3-b981-6f04ea4657b0

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s19_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r0_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 0 19 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 1)
    0 0 parentExponent_s19_r0_i0 compatibilityExponent_s19_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 0 19 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r0_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 9, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 0 19 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 2)
    1 0 parentExponent_s19_r0_i1 compatibilityExponent_s19_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 0 19 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r1_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 0 19 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 1)
    0 1 parentExponent_s19_r1_i0 compatibilityExponent_s19_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 0 19 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r1_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r1_i1 :
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
    1 1 parentExponent_s19_r1_i1 compatibilityExponent_s19_r1_i1 (2 / 5)
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

private def parentExponent_s19_r2_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r2_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r2_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 0 19 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 1)
    0 2 parentExponent_s19_r2_i0 compatibilityExponent_s19_r2_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 0 19 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r2_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r2_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 9, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r2_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 0 19 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 2)
    1 2 parentExponent_s19_r2_i1 compatibilityExponent_s19_r2_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 0 19 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r3_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r3_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r3_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 0 19 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 1)
    0 3 parentExponent_s19_r3_i0 compatibilityExponent_s19_r3_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 0 19 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 0 19 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r3_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r3_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s19_r3_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 0 19 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 0 19) (splitCount 0 19) (integerProfile 0 19 2)
    1 3 parentExponent_s19_r3_i1 compatibilityExponent_s19_r3_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 0 19 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

/-- Both directional compatibility margins for each nonempty region
of released owner 0, recipe 19. -/
theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 0 19).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 0 19 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 0 19 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s19_r0_i0
    · exact region_s19_r0_i1
  · fin_cases i
    · exact region_s19_r1_i0
    · exact region_s19_r1_i1
  · fin_cases i
    · exact region_s19_r2_i0
    · exact region_s19_r2_i1
  · fin_cases i
    · exact region_s19_r3_i0
    · exact region_s19_r3_i1
  · have hz : (seed 0 19).region.getD 4 0 = 0 := by decide +kernel
    change 0 < (seed 0 19).region.getD 4 0 at hn
    rw [hz] at hn
    exact False.elim ((lt_irrefl 0) hn)
  · have hz : (seed 0 19).region.getD 5 0 = 0 := by decide +kernel
    change 0 < (seed 0 19).region.getD 5 0 at hn
    rw [hz] at hn
    exact False.elim ((lt_irrefl 0) hn)


#print axioms solution
