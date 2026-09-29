-- Prove2me | solution 1 for mme_released_interior_owner2_shape21_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:53:01.800136+00:00
-- url     : https://prove2.me/submissions/a19ee31a-58d4-4050-ad93-33216b59a4e0

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s21_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r0_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 2 21 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 0 parentExponent_s21_r0_i0 compatibilityExponent_s21_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 2 21 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r0_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 17, 0, 0, 0, 17, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 2 21 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 0 parentExponent_s21_r0_i1 compatibilityExponent_s21_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 2 21 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r1_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 2 21 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 1 parentExponent_s21_r1_i0 compatibilityExponent_s21_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 2 21 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r1_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 17, 0, 0, 0, 17, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 23, 0, 0, 0, 23, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r1_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 2 21 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 1 parentExponent_s21_r1_i1 compatibilityExponent_s21_r1_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 2 21 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r2_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r2_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r2_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 2 21 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 2 parentExponent_s21_r2_i0 compatibilityExponent_s21_r2_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 2 21 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r2_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r2_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r2_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 2 21 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 2 parentExponent_s21_r2_i1 compatibilityExponent_s21_r2_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 2 21 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r3_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r3_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r3_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 2 21 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 3 parentExponent_s21_r3_i0 compatibilityExponent_s21_r3_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 2 21 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r3_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r3_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r3_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 2 21 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 3 parentExponent_s21_r3_i1 compatibilityExponent_s21_r3_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 2 21 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r4_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r4_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r4_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 2 21 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 4 parentExponent_s21_r4_i0 compatibilityExponent_s21_r4_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 2 21 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r4_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r4_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r4_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 2 21 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 4 parentExponent_s21_r4_i1 compatibilityExponent_s21_r4_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 2 21 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r5_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r5_i0
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r5_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 2 21 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 1)
    0 5 parentExponent_s21_r5_i0 compatibilityExponent_s21_r5_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 2 21 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 2 21 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s21_r5_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s21_r5_i1
    (t : MME.ReleasedInterior.Split 21 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 2 21).splits.idxOf (sourceShape 2 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

/-- The actual released parent mixture and local compatibility partition
have normalized entropy difference at least two fifths in this region. -/
private theorem region_s21_r5_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 2 21 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 21)
    (regionalSize 2 21) (splitCount 2 21) (integerProfile 2 21 2)
    1 5 parentExponent_s21_r5_i1 compatibilityExponent_s21_r5_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 2 21 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 2 21 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

/-- Both directional compatibility margins for each nonempty region
of released owner 2, recipe 21. -/
theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 2 21).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 2 21 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 2 21 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s21_r0_i0
    · exact region_s21_r0_i1
  · fin_cases i
    · exact region_s21_r1_i0
    · exact region_s21_r1_i1
  · fin_cases i
    · exact region_s21_r2_i0
    · exact region_s21_r2_i1
  · fin_cases i
    · exact region_s21_r3_i0
    · exact region_s21_r3_i1
  · fin_cases i
    · exact region_s21_r4_i0
    · exact region_s21_r4_i1
  · fin_cases i
    · exact region_s21_r5_i0
    · exact region_s21_r5_i1


#print axioms solution
