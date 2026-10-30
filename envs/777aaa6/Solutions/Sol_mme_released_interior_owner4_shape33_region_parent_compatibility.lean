-- Prove2me | solution 1 for mme_released_interior_owner4_shape33_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:51:47.732008+00:00
-- url     : https://prove2.me/submissions/14dfe814-d404-48cc-a420-e08f47c660c9

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s33_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r0_i0
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 33 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 1)
    0 0 parentExponent_s33_r0_i0 compatibilityExponent_s33_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 33 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s33_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r0_i1
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 33 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 2)
    1 0 parentExponent_s33_r0_i1 compatibilityExponent_s33_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 33 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s33_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r1_i0
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 33 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 1)
    0 1 parentExponent_s33_r1_i0 compatibilityExponent_s33_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 33 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s33_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r1_i1
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r1_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 33 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 2)
    1 1 parentExponent_s33_r1_i1 compatibilityExponent_s33_r1_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 33 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s33_r2_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r2_i0
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r2_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 4 33 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 1)
    0 2 parentExponent_s33_r2_i0 compatibilityExponent_s33_r2_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 33 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 4 33 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s33_r2_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s33_r2_i1
    (t : MME.ReleasedInterior.Split 33 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s33_r2_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 4 33 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 33)
    (regionalSize 4 33) (splitCount 4 33) (integerProfile 4 33 2)
    1 2 parentExponent_s33_r2_i1 compatibilityExponent_s33_r2_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 33 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 4 33 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 4 33).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 33) (regionalSize 4 33)
        (splitCount 4 33) (integerProfile 4 33 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 33) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 4 33 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 4 33 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s33_r0_i0
    · exact region_s33_r0_i1
  · fin_cases i
    · exact region_s33_r1_i0
    · exact region_s33_r1_i1
  · fin_cases i
    · exact region_s33_r2_i0
    · exact region_s33_r2_i1
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
