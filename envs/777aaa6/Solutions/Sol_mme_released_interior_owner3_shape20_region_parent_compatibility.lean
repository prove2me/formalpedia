-- Prove2me | solution 1 for mme_released_interior_owner3_shape20_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T01:20:28.79307+00:00
-- url     : https://prove2.me/submissions/b9a9b171-c100-46f9-a7c3-6545a021f39a

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s20_r0_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r0_i0
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r0_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 20 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 1)
    0 0 parentExponent_s20_r0_i0 compatibilityExponent_s20_r0_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨0, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 20 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r0_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r0_i1
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r0_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 20 0) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 2)
    1 0 parentExponent_s20_r0_i1 compatibilityExponent_s20_r0_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 0) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨0, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨0, c⟩ w) t w : ℝ) /
        regionalSize 3 20 0) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r1_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r1_i0
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r1_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 3 20 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 1)
    0 1 parentExponent_s20_r1_i0 compatibilityExponent_s20_r1_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨1, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 3 20 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r1_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r1_i1
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 6, 0, 0, 0, 6, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r1_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 3 20 1) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 2)
    1 1 parentExponent_s20_r1_i1 compatibilityExponent_s20_r1_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 3 20 1) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r4_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r4_i0
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r4_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 3 20 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 1)
    0 4 parentExponent_s20_r4_i0 compatibilityExponent_s20_r4_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨4, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 3 20 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r4_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r4_i1
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 7, 0, 0, 0, 7, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r4_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 3 20 4) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 2)
    1 4 parentExponent_s20_r4_i1 compatibilityExponent_s20_r4_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 4) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨4, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨4, c⟩ w) t w : ℝ) /
        regionalSize 3 20 4) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r5_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 0, 0, 7, 0, 2, 0, 7, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r5_i0
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 5, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r5_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 3 20 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 1)
    0 5 parentExponent_s20_r5_i0 compatibilityExponent_s20_r5_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 3 20 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 3 20 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s20_r5_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 7, 0, 7, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s20_r5_i1
    (t : MME.ReleasedInterior.Split 20 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0]].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s20_r5_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 3 20 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 20)
    (regionalSize 3 20) (splitCount 3 20) (integerProfile 3 20 2)
    1 5 parentExponent_s20_r5_i1 compatibilityExponent_s20_r5_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 3 20 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 3 20 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 3 20).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 20) (regionalSize 3 20)
        (splitCount 3 20) (integerProfile 3 20 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 20) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 3 20 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 3 20 r) := by
  fin_cases r
  · fin_cases i
    · exact region_s20_r0_i0
    · exact region_s20_r0_i1
  · fin_cases i
    · exact region_s20_r1_i0
    · exact region_s20_r1_i1
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s20_r4_i0
    · exact region_s20_r4_i1
  · fin_cases i
    · exact region_s20_r5_i0
    · exact region_s20_r5_i1
