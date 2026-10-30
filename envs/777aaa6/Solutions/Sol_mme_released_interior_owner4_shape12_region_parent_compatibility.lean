-- Prove2me | solution 1 for mme_released_interior_owner4_shape12_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:15:54.504994+00:00
-- url     : https://prove2.me/submissions/0713b01e-ddf8-4659-b53e-64c7a42f50e3

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s12_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r0_i0
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 12 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 1)
    0 0 parentExponent_s12_r0_i0 compatibilityExponent_s12_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 12 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s12_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r0_i1
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 11, 0, 0, 0, 11, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 12 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 2)
    1 0 parentExponent_s12_r0_i1 compatibilityExponent_s12_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 4 12 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s12_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r1_i0
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 12 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 1)
    0 1 parentExponent_s12_r1_i0 compatibilityExponent_s12_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 12 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s12_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r1_i1
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 12, 0, 0, 0, 12, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r1_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 12 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 2)
    1 1 parentExponent_s12_r1_i1 compatibilityExponent_s12_r1_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 4 12 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s12_r4_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r4_i0
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r4_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 12 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 1)
    0 4 parentExponent_s12_r4_i0 compatibilityExponent_s12_r4_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 4 12 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 12 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s12_r4_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s12_r4_i1
    (t : MME.ReleasedInterior.Split 12 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0]].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 12, 0, 0, 0, 12, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s12_r4_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 12 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 12)
    (regionalSize 4 12) (splitCount 4 12) (integerProfile 4 12 2)
    1 4 parentExponent_s12_r4_i1 compatibilityExponent_s12_r4_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 4 12 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 4 12 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 4 12).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 12) (regionalSize 4 12)
        (splitCount 4 12) (integerProfile 4 12 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 12) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 4 12 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 4 12 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s12_r0_i0
    · exact region_s12_r0_i1
  · fin_cases i
    · exact region_s12_r1_i0
    · exact region_s12_r1_i1
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s12_r4_i0
    · exact region_s12_r4_i1
  · exact absurd hn (by decide +kernel)
