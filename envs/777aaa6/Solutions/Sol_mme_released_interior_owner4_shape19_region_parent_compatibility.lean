-- Prove2me | solution 1 for mme_released_interior_owner4_shape19_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:37:21.141709+00:00
-- url     : https://prove2.me/submissions/17930b32-4751-42d6-8b2c-577b3a89e25d

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
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 19 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 1)
    0 0 parentExponent_s19_r0_i0 compatibilityExponent_s19_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 19 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r0_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 19 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 2)
    1 0 parentExponent_s19_r0_i1 compatibilityExponent_s19_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 19 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r1_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 19 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 1)
    0 1 parentExponent_s19_r1_i0 compatibilityExponent_s19_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 19 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r1_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 9, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r1_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 19 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 2)
    1 1 parentExponent_s19_r1_i1 compatibilityExponent_s19_r1_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 19 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r4_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r4_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r4_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 19 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 1)
    0 4 parentExponent_s19_r4_i0 compatibilityExponent_s19_r4_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 19 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r4_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10, 0, 6, 0, 10, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r4_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 9, 0, 0, 0, 9, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r4_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 19 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 2)
    1 4 parentExponent_s19_r4_i1 compatibilityExponent_s19_r4_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 19 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r5_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 8, 0, 3, 0, 8, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r5_i0
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r5_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 4 19 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 1)
    0 5 parentExponent_s19_r5_i0 compatibilityExponent_s19_r5_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 19 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 4 19 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s19_r5_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 11, 0, 6, 0, 11, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s19_r5_i1
    (t : MME.ReleasedInterior.Split 19 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0]].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s19_r5_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 4 19 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 19)
    (regionalSize 4 19) (splitCount 4 19) (integerProfile 4 19 2)
    1 5 parentExponent_s19_r5_i1 compatibilityExponent_s19_r5_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 19 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 4 19 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 4 19).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 4 19)
        (splitCount 4 19) (integerProfile 4 19 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 4 19 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 4 19 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s19_r0_i0
    · exact region_s19_r0_i1
  · fin_cases i
    · exact region_s19_r1_i0
    · exact region_s19_r1_i1
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s19_r4_i0
    · exact region_s19_r4_i1
  · fin_cases i
    · exact region_s19_r5_i0
    · exact region_s19_r5_i1
