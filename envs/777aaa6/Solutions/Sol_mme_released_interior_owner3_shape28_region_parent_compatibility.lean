-- Prove2me | solution 1 for mme_released_interior_owner3_shape28_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:22:40.720044+00:00
-- url     : https://prove2.me/submissions/d49d0b39-cf80-4064-81dd-9e4f35d7c9d4

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s28_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r0_i0
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 11, 0, 0, 0, 11, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 28 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 1)
    0 0 parentExponent_s28_r0_i0 compatibilityExponent_s28_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 28 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s28_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r0_i1
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 28 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 2)
    1 0 parentExponent_s28_r0_i1 compatibilityExponent_s28_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 28 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s28_r2_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r2_i0
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 11, 0, 0, 0, 11, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r2_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 3 28 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 1)
    0 2 parentExponent_s28_r2_i0 compatibilityExponent_s28_r2_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 3 28 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s28_r2_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r2_i1
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r2_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 3 28 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 2)
    1 2 parentExponent_s28_r2_i1 compatibilityExponent_s28_r2_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 3 28 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s28_r3_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r3_i0
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 10, 0, 0, 0, 10, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r3_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 3 28 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 1)
    0 3 parentExponent_s28_r3_i0 compatibilityExponent_s28_r3_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 28 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 3 28 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s28_r3_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s28_r3_i1
    (t : MME.ReleasedInterior.Split 28 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s28_r3_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 3 28 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 28)
    (regionalSize 3 28) (splitCount 3 28) (integerProfile 3 28 2)
    1 3 parentExponent_s28_r3_i1 compatibilityExponent_s28_r3_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 28 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 3 28 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 3 28).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 3 28)
        (splitCount 3 28) (integerProfile 3 28 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 3 28 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 3 28 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s28_r0_i0
    · exact region_s28_r0_i1
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s28_r2_i0
    · exact region_s28_r2_i1
  · fin_cases i
    · exact region_s28_r3_i0
    · exact region_s28_r3_i1
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
