-- Prove2me | solution 1 for mme_released_interior_owner5_shape11_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T08:14:54.494014+00:00
-- url     : https://prove2.me/submissions/bcf02577-7600-437f-a2d3-5f2837c2ed38

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

private def wordIndex (w : CompleteWord 2) : ℕ := 3 * (w 0).val + (w 1).val

private def parentExponent_s11_r2_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r2_i0
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r2_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 5 11 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 1)
    0 2 parentExponent_s11_r2_i0 compatibilityExponent_s11_r2_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨2, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 5 11 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s11_r2_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r2_i1
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r2_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 5 11 2) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 2)
    1 2 parentExponent_s11_r2_i1 compatibilityExponent_s11_r2_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 2) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨2, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨2, c⟩ w) t w : ℝ) /
        regionalSize 5 11 2) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s11_r3_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r3_i0
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r3_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 5 11 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 1)
    0 3 parentExponent_s11_r3_i0 compatibilityExponent_s11_r3_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨3, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 5 11 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s11_r3_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r3_i1
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r3_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 5 11 3) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 2)
    1 3 parentExponent_s11_r3_i1 compatibilityExponent_s11_r3_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 3) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨3, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨3, c⟩ w) t w : ℝ) /
        regionalSize 5 11 3) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s11_r5_i0 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 7, 0, 3, 0, 7, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r5_i0
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r5_i0 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 5 11 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 1)
    0 5 parentExponent_s11_r5_i0 compatibilityExponent_s11_r5_i0 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 1) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 0 ⟨5, c⟩)
          (fun c => c.val (yzMode 0))
          (fun c w => integerProfile 5 11 1 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 5 11 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

private def parentExponent_s11_r5_i1 (w : Fin 2 → CompleteWord 2) : ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 0, 0, 0, 8, 0, 2, 0, 8, 0, 0, 0, 8, 0, 8, 0, 0, 0, 0, 0].getD (9 * wordIndex (w 0) + wordIndex (w 1)) 0

private def compatibilityExponent_s11_r5_i1
    (t : MME.ReleasedInterior.Split 11 ⊕ Fin 5)
    (w : CompleteWord 2) : ℕ :=
  match t with
  | Sum.inl c =>
    ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 4, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) []).getD
      (wordIndex w) 0
  | Sum.inr j => ([[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]].getD j.val []).getD (wordIndex w) 0

private theorem region_s11_r5_i1 :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 5 11 5) := by
  have h := mme_rational_parent_compatibility_certificate (parent_total 11)
    (regionalSize 5 11) (splitCount 5 11) (integerProfile 5 11 2)
    1 5 parentExponent_s11_r5_i1 compatibilityExponent_s11_r5_i1 (2 / 5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 2) 5) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) 1 ⟨5, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 5 11 2 ⟨5, c⟩ w) t w : ℝ) /
        regionalSize 5 11 5) := by
    apply h
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

theorem solution
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 5 11).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 11) (regionalSize 5 11)
        (splitCount 5 11) (integerProfile 5 11 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 11) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 5 11 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 5 11 r) := by
  fin_cases r
  · exact absurd hn (by decide +kernel)
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s11_r2_i0
    · exact region_s11_r2_i1
  · fin_cases i
    · exact region_s11_r3_i0
    · exact region_s11_r3_i1
  · exact absurd hn (by decide +kernel)
  · fin_cases i
    · exact region_s11_r5_i0
    · exact region_s11_r5_i1
