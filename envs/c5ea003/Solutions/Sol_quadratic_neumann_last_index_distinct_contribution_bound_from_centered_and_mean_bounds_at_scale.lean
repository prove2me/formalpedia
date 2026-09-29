-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_contribution_bound_from_centered_and_mean_bounds_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:57:09.204142+00:00
-- url     : https://prove2.me/submissions/3d703727-04e0-450f-a53a-136637f94a23

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X + Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) +
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_add_le _ _

private lemma centeredIndicator_sq
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    centeredIndicator Omega p i j ^ 2 =
      (1 - 2 * p) * centeredIndicator Omega p i j + p * (1 - p) := by
  by_cases h : (i, j) ∈ Omega
  · simp [centeredIndicator, h]
    ring
  · simp [centeredIndicator, h]
    ring

private lemma double_sum_ite_smul_coordinateMatrix_apply
    {n₁ n₂ : ℕ} (f : Fin n₁ × Fin n₂ → Fin n₁ × Fin n₂ → ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    (∑ w1 : Fin n₁ × Fin n₂,
        ∑ w2 : Fin n₁ × Fin n₂,
          if w1 = w2 then 0 else f w1 w2 • coordinateMatrix w1.1 w1.2) i j =
      ∑ w2 : Fin n₁ × Fin n₂,
        if (i, j) = w2 then 0 else f (i, j) w2 := by
  rw [Matrix.sum_apply]
  simp only [Matrix.sum_apply]
  calc
    ∑ x : Fin n₁ × Fin n₂,
        ∑ w2 : Fin n₁ × Fin n₂,
          (if x = w2 then 0 else f x w2 • coordinateMatrix x.1 x.2) i j
        = ∑ w2 : Fin n₁ × Fin n₂,
            (if (i, j) = w2 then 0
              else f (i, j) w2 • coordinateMatrix (i, j).1 (i, j).2) i j := by
          refine Finset.sum_eq_single (i, j) ?_ ?_
          · intro x _hx hne
            have hnot : ¬ (x.1 = i ∧ x.2 = j) := by
              intro h
              apply hne
              ext <;> simp [h.1, h.2]
            refine Finset.sum_eq_zero ?_
            intro w2 _hw2
            by_cases hxw : x = w2
            · subst x
              simp
            · have hnot' : ¬ (i = x.1 ∧ j = x.2) := by
                intro h
                exact hnot ⟨h.1.symm, h.2.symm⟩
              have hcoord : coordinateMatrix x.1 x.2 i j = 0 := by
                simp [coordinateMatrix, hnot']
              simp [hxw, hcoord]
          · intro hmem
            simp at hmem
    _ = ∑ w2 : Fin n₁ × Fin n₂,
          if (i, j) = w2 then 0 else f (i, j) w2 := by
        refine Finset.sum_congr rfl ?_
        intro w2 _hw2
        by_cases h : (i, j) = w2
        · simp [h]
        · simp [h, coordinateMatrix]

private lemma last_index_distinct_decomposition
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    quadraticNeumannLastIndexDistinctContribution Omega S p =
      quadraticNeumannLastIndexDistinctCenteredContribution Omega S p +
        quadraticNeumannLastIndexDistinctMeanContribution Omega S p := by
  ext i j
  simp [quadraticNeumannLastIndexDistinctContribution,
    quadraticNeumannLastIndexDistinctCenteredContribution,
    quadraticNeumannLastIndexDistinctMeanContribution,
    double_sum_ite_smul_coordinateMatrix_apply]
  by_cases hp : p = 0
  · simp [hp]
  · calc
      (p ^ 3)⁻¹ *
          (∑ w2 : Fin n₁ × Fin n₂,
            if (i, j) = w2 then 0
            else
              centeredIndicator Omega p i j ^ 2 *
                centeredIndicator Omega p w2.1 w2.2 *
                  signMatrix S w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 i j *
                      tangentCoordinateKernel S i j i j) =
        ∑ w2 : Fin n₁ × Fin n₂,
          (p ^ 3)⁻¹ *
            (if (i, j) = w2 then 0
            else
              centeredIndicator Omega p i j ^ 2 *
                centeredIndicator Omega p w2.1 w2.2 *
                  signMatrix S w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 i j *
                      tangentCoordinateKernel S i j i j) := by
          rw [Finset.mul_sum]
      _ =
        ∑ w2 : Fin n₁ × Fin n₂,
          (((p ^ 3)⁻¹ *
            (if (i, j) = w2 then 0
            else
              (1 - 2 * p) * centeredIndicator Omega p i j *
                centeredIndicator Omega p w2.1 w2.2 *
                  signMatrix S w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 i j *
                      tangentCoordinateKernel S i j i j)) +
          ((p ^ 2)⁻¹ *
            (if (i, j) = w2 then 0
            else
              (1 - p) * centeredIndicator Omega p w2.1 w2.2 *
                signMatrix S w2.1 w2.2 *
                  tangentCoordinateKernel S w2.1 w2.2 i j *
                    tangentCoordinateKernel S i j i j))) := by
          refine Finset.sum_congr rfl ?_
          intro w2 _hw2
          by_cases h : (i, j) = w2
          · simp [h]
          · simp [h, centeredIndicator_sq Omega p i j]
            field_simp [hp]
      _ =
        (p ^ 3)⁻¹ *
            (∑ w2 : Fin n₁ × Fin n₂,
              (if (i, j) = w2 then 0
              else
                (1 - 2 * p) * centeredIndicator Omega p i j *
                  centeredIndicator Omega p w2.1 w2.2 *
                    signMatrix S w2.1 w2.2 *
                      tangentCoordinateKernel S w2.1 w2.2 i j *
                        tangentCoordinateKernel S i j i j)) +
          (p ^ 2)⁻¹ *
            (∑ w2 : Fin n₁ × Fin n₂,
              (if (i, j) = w2 then 0
              else
                (1 - p) * centeredIndicator Omega p w2.1 w2.2 *
                  signMatrix S w2.1 w2.2 *
                    tangentCoordinateKernel S w2.1 w2.2 i j *
                      tangentCoordinateKernel S i j i j)) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.mul_sum]

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p Ccent Cmean scale : ℝ) :
    spectralNorm
        (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) ≤
      Ccent * scale →
    spectralNorm
        (quadraticNeumannLastIndexDistinctMeanContribution Omega S p) ≤
      Cmean * scale →
    spectralNorm (quadraticNeumannLastIndexDistinctContribution Omega S p) ≤
      (Ccent + Cmean) * scale := by
  intro hcent hmean
  rw [last_index_distinct_decomposition S Omega p]
  calc
    spectralNorm
        (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p +
          quadraticNeumannLastIndexDistinctMeanContribution Omega S p)
        ≤ spectralNorm
            (quadraticNeumannLastIndexDistinctCenteredContribution Omega S p) +
          spectralNorm
            (quadraticNeumannLastIndexDistinctMeanContribution Omega S p) :=
        spectralNorm_add_le _ _
    _ ≤ Ccent * scale + Cmean * scale := add_le_add hcent hmean
    _ = (Ccent + Cmean) * scale := by ring
