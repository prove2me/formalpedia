-- Prove2me | solution 1 for tangent_sampling_deviation_le_nested_dual_supremum_of_nonnegative_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T08:10:27.292628+00:00
-- url     : https://prove2.me/submissions/8130be26-4839-453e-b18e-c540b1b7c2b2

import Definitions.Def_matrix_completion_talagrand_nested_dual
import Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MatrixCompletion
open scoped Classical BigOperators

private theorem matrix_inner_le_frobenius_mul {n₁ n₂ : ℕ}
    (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner X Y ≤ frobeniusNorm X * frobeniusNorm Y := by
  have hsq : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    unfold matrixInner frobeniusNormSq
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n₁ × Fin n₂))
      (fun p : Fin n₁ × Fin n₂ => X p.1 p.2)
      (fun p : Fin n₁ × Fin n₂ => Y p.1 p.2)
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    rw [Fintype.sum_prod_type] at h
    simpa using h
  have hx0 : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have habs :
      |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := by
    rw [← Real.sqrt_sq_eq_abs (matrixInner X Y)]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt :
      Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) =
        frobeniusNorm X * frobeniusNorm Y := by
    unfold frobeniusNorm
    rw [Real.sqrt_mul hx0]
  exact le_trans (le_abs_self (matrixInner X Y)) (by simpa [hsqrt] using habs)

private theorem scaled_matrix_inner_le_scaled_frobenius_of_unit {n₁ n₂ : ℕ}
    (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) (p : ℝ) :
    0 ≤ p →
    frobeniusNorm X ≤ 1 →
    p⁻¹ * matrixInner X Y ≤ p⁻¹ * frobeniusNorm Y := by
  intro hp hX
  have hinv : 0 ≤ p⁻¹ := inv_nonneg.mpr hp
  have hnonnegY : 0 ≤ frobeniusNorm Y := by
    unfold frobeniusNorm
    positivity
  have hinner : matrixInner X Y ≤ frobeniusNorm Y := by
    calc
      matrixInner X Y ≤ frobeniusNorm X * frobeniusNorm Y :=
        matrix_inner_le_frobenius_mul X Y
      _ ≤ 1 * frobeniusNorm Y := mul_le_mul_of_nonneg_right hX hnonnegY
      _ = frobeniusNorm Y := one_mul _
  exact mul_le_mul_of_nonneg_left hinner hinv

private theorem frobeniusNorm_smul {n₁ n₂ : ℕ} (c : ℝ)
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm (c • Y) = |c| * frobeniusNorm Y := by
  unfold frobeniusNorm frobeniusNormSq
  have hsum : (∑ i : Fin n₁, ∑ j : Fin n₂, (c * Y i j) ^ 2) =
      c ^ 2 * (∑ i : Fin n₁, ∑ j : Fin n₂, Y i j ^ 2) := by
    simp [mul_pow, Finset.mul_sum]
  rw [show (∑ i : Fin n₁, ∑ j : Fin n₂, (c • Y) i j ^ 2) =
      (∑ i : Fin n₁, ∑ j : Fin n₂, (c * Y i j) ^ 2) by
    simp [Matrix.smul_apply, smul_eq_mul]]
  rw [hsum]
  rw [Real.sqrt_mul]
  · rw [Real.sqrt_sq_eq_abs]
  · positivity

private theorem matrixInner_self_eq_frobeniusNormSq {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner Y Y = frobeniusNormSq Y := by
  unfold matrixInner frobeniusNormSq
  simp [sq]

private theorem frobeniusNormSq_eq_norm_sq {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq Y = frobeniusNorm Y ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt]
  unfold frobeniusNormSq
  positivity

private theorem normalized_frobenius_le_one {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm ((frobeniusNorm Y)⁻¹ • Y) ≤ 1 := by
  rw [frobeniusNorm_smul]
  have hnonneg : 0 ≤ frobeniusNorm Y := by
    unfold frobeniusNorm
    positivity
  by_cases hzero : frobeniusNorm Y = 0
  · simp [hzero]
  · rw [abs_of_nonneg (inv_nonneg.mpr hnonneg)]
    rw [inv_mul_cancel₀ hzero]

private theorem matrixInner_normalized_self {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hY : frobeniusNorm Y ≠ 0) :
    matrixInner ((frobeniusNorm Y)⁻¹ • Y) Y = frobeniusNorm Y := by
  rw [show matrixInner ((frobeniusNorm Y)⁻¹ • Y) Y =
      (frobeniusNorm Y)⁻¹ * matrixInner Y Y by
    unfold matrixInner
    simp [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_assoc]]
  rw [matrixInner_self_eq_frobeniusNormSq]
  rw [frobeniusNormSq_eq_norm_sq]
  field_simp [hY]

private theorem scaled_frobenius_le_dual_sup {n₁ n₂ : ℕ}
    (Y : Matrix (Fin n₁) (Fin n₂) ℝ) (p : ℝ) :
    0 ≤ p →
    p⁻¹ * frobeniusNorm Y ≤
      sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧ w = p⁻¹ * matrixInner X1 Y} := by
  intro hp
  have hbdd : BddAbove {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧ w = p⁻¹ * matrixInner X1 Y} := by
    refine ⟨p⁻¹ * frobeniusNorm Y, ?_⟩
    intro w hw
    rcases hw with ⟨X1, hX1, rfl⟩
    exact scaled_matrix_inner_le_scaled_frobenius_of_unit X1 Y p hp hX1
  by_cases hY : frobeniusNorm Y = 0
  · have hmem : (0 : ℝ) ∈ {w : ℝ |
        ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
          frobeniusNorm X1 ≤ 1 ∧ w = p⁻¹ * matrixInner X1 Y} := by
      refine ⟨0, ?_, ?_⟩
      · unfold frobeniusNorm frobeniusNormSq
        simp
      · simp [matrixInner]
    simpa [hY] using le_csSup hbdd hmem
  · have hmem : p⁻¹ * frobeniusNorm Y ∈ {w : ℝ |
        ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
          frobeniusNorm X1 ≤ 1 ∧ w = p⁻¹ * matrixInner X1 Y} := by
      refine ⟨(frobeniusNorm Y)⁻¹ • Y, normalized_frobenius_le_one Y, ?_⟩
      rw [matrixInner_normalized_self Y hY]
    exact le_csSup hbdd hmem

private theorem tangentSamplingNestedDualDeviation_candidates_bddAbove
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    BddAbove {v : ℝ |
      ∃ X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X2 = X2 ∧
          frobeniusNorm X2 ≤ 1 ∧
            v =
              sSup {w : ℝ |
                ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
                  frobeniusNorm X1 ≤ 1 ∧
                    w =
                      p⁻¹ *
                        matrixInner X1
                          (tangentProjection S (samplingProjection Omega X2) -
                            p • X2)}} := by
  intro hp
  refine ⟨tangentSamplingDeviation Omega S p, ?_⟩
  intro b hb
  rcases hb with ⟨X2, hT, hX2, rfl⟩
  refine csSup_le ?inner_nonempty ?inner_le
  · refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · unfold frobeniusNorm frobeniusNormSq
      simp
    · simp [matrixInner]
  · intro w hw
    rcases hw with ⟨X1, hX1, rfl⟩
    have hscaled :=
      scaled_matrix_inner_le_scaled_frobenius_of_unit X1
        (tangentProjection S (samplingProjection Omega X2) - p • X2) p hp hX1
    refine le_trans hscaled ?_
    unfold tangentSamplingDeviation
    refine le_csSup (tangent_sampling_deviation_candidates_bddAbove Omega S p) ?_
    exact ⟨X2, hT, hX2, rfl⟩

/-- One direction of the Frobenius-duality rewrite for the tangent sampling
deviation.

For `0 <= p`, the scaled Frobenius norm in `tangentSamplingDeviation` is
bounded by the nested supremum over Frobenius-unit dual test matrices.  This is
the direction that says the dual unit ball contains enough tests to recover
the norm.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2), where the paper rewrites `Z` as `sup <X_1,Y(X_2)>`.  The analytic input
is finite-dimensional Frobenius norm duality. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p ≤
      tangentSamplingNestedDualDeviation Omega S p := by
  intro hp
  unfold tangentSamplingDeviation tangentSamplingNestedDualDeviation
  refine csSup_le ?dev_nonempty ?dev_le
  · refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · ext i j
      simp [tangentProjection, leftSingularProjection, rightSingularProjection,
        twoSidedSingularProjection]
    · unfold frobeniusNorm frobeniusNormSq
      simp
    · simp [tangentProjection, leftSingularProjection, rightSingularProjection,
        twoSidedSingularProjection, samplingProjection, frobeniusNorm, frobeniusNormSq]
  · intro b hb
    rcases hb with ⟨X2, hT, hX2, rfl⟩
    have hdual :=
      scaled_frobenius_le_dual_sup
        (tangentProjection S (samplingProjection Omega X2) - p • X2) p hp
    refine le_trans hdual ?_
    refine le_csSup (tangentSamplingNestedDualDeviation_candidates_bddAbove Omega S p hp) ?_
    exact ⟨X2, hT, hX2, rfl⟩
