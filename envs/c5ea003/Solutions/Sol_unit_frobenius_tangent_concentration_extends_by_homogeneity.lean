-- Prove2me | solution 1 for unit_frobenius_tangent_concentration_extends_by_homogeneity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:54:23.516781+00:00
-- url     : https://prove2.me/submissions/0764b3ef-12e5-49b8-93a2-7e0d15883b8f

import Definitions.Def_matrix_completion_tangent
import Mathlib.Tactic

open MatrixCompletion

private lemma frobeniusNormSq_smul
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq (a • X) = a ^ 2 * frobeniusNormSq X := by
  unfold frobeniusNormSq
  simp [Finset.mul_sum]
  ring_nf

private lemma frobeniusNorm_smul
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm (a • X) = |a| * frobeniusNorm X := by
  unfold frobeniusNorm
  rw [frobeniusNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg a)]
  rw [Real.sqrt_sq_eq_abs]

private lemma frobenius_norm_zero_implies_matrix_zero_local
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNorm X = 0 → X = 0 := by
  intro hnorm
  ext i j
  have hsumsq_zero : frobeniusNormSq X = 0 := by
    have hsqrt_sq := congrArg (fun x : ℝ => x ^ 2) hnorm
    have hnonneg : 0 ≤ frobeniusNormSq X := by
      unfold frobeniusNormSq
      positivity
    simpa [frobeniusNorm, Real.sq_sqrt hnonneg] using hsqrt_sq
  have hrow_nonneg : ∀ i : Fin n₁, 0 ≤ ∑ j : Fin n₂, X i j ^ 2 := by
    intro i
    positivity
  have hrow_zero : ∑ j : Fin n₂, X i j ^ 2 = 0 := by
    have hle :
        ∑ j : Fin n₂, X i j ^ 2 ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, X i j ^ 2 := by
      exact Finset.single_le_sum (fun x _ => hrow_nonneg x) (Finset.mem_univ i)
    unfold frobeniusNormSq at hsumsq_zero
    linarith [hrow_nonneg i]
  have hentry_nonneg : ∀ j : Fin n₂, 0 ≤ X i j ^ 2 := by
    intro j
    positivity
  have hentry_zero : X i j ^ 2 = 0 := by
    have hle : X i j ^ 2 ≤ ∑ j : Fin n₂, X i j ^ 2 := by
      exact Finset.single_le_sum (fun x _ => hentry_nonneg x) (Finset.mem_univ j)
    linarith [hentry_nonneg j]
  exact sq_eq_zero_iff.mp hentry_zero

private lemma samplingProjection_smul
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) (a : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    samplingProjection Omega (a • X) = a • samplingProjection Omega X := by
  ext i j
  simp [samplingProjection]

private lemma leftSingularProjection_smul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    leftSingularProjection S (a • X) =
      a • leftSingularProjection S X := by
  ext i j
  unfold leftSingularProjection
  change (∑ a_1 : Fin n₁,
      (∑ k : Fin r, S.u k i * S.u k a_1) * (a * X a_1 j)) =
    a * ∑ a_1 : Fin n₁,
      (∑ k : Fin r, S.u k i * S.u k a_1) * X a_1 j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private lemma rightSingularProjection_smul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    rightSingularProjection S (a • X) =
      a • rightSingularProjection S X := by
  ext i j
  unfold rightSingularProjection
  change (∑ b : Fin n₂,
      (a * X i b) * (∑ k : Fin r, S.v k b * S.v k j)) =
    a * ∑ b : Fin n₂,
      X i b * (∑ k : Fin r, S.v k b * S.v k j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private lemma twoSidedSingularProjection_smul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    twoSidedSingularProjection S (a • X) =
      a • twoSidedSingularProjection S X := by
  ext i j
  unfold twoSidedSingularProjection
  change (∑ a_1 : Fin n₁, ∑ b : Fin n₂,
      (∑ k : Fin r, S.u k i * S.u k a_1) * (a * X a_1 b) *
        (∑ l : Fin r, S.v l b * S.v l j)) =
    a * ∑ a_1 : Fin n₁, ∑ b : Fin n₂,
      (∑ k : Fin r, S.u k i * S.u k a_1) * X a_1 b *
        (∑ l : Fin r, S.v l b * S.v l j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private lemma tangentProjection_smul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S (a • X) = a • tangentProjection S X := by
  ext i j
  simp [tangentProjection, leftSingularProjection_smul,
    rightSingularProjection_smul, twoSidedSingularProjection_smul]
  ring

private lemma tangent_sampling_fluctuation_smul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S (samplingProjection Omega (a • X)) -
        p • (a • X) =
      a • (tangentProjection S (samplingProjection Omega X) - p • X) := by
  rw [samplingProjection_smul, tangentProjection_smul]
  ext i j
  simp
  ring

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 ≤ p →
    (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p) →
    TangentSamplingConcentration Omega S p epsilon := by
  intro _hp hUnit X hTangent
  by_cases hzero : frobeniusNorm X = 0
  · have hXzero : X = 0 :=
      frobenius_norm_zero_implies_matrix_zero_local X hzero
    subst X
    simp [samplingProjection, tangentProjection,
      leftSingularProjection, rightSingularProjection,
      twoSidedSingularProjection, frobeniusNorm, frobeniusNormSq]
  · have hnorm_nonneg : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
    have hnorm_pos : 0 < frobeniusNorm X := by
      exact lt_of_le_of_ne hnorm_nonneg (Ne.symm hzero)
    let Y : Matrix (Fin n₁) (Fin n₂) ℝ := (frobeniusNorm X)⁻¹ • X
    have hYtangent : tangentProjection S Y = Y := by
      dsimp [Y]
      rw [tangentProjection_smul, hTangent]
    have hYnorm : frobeniusNorm Y = 1 := by
      dsimp [Y]
      rw [frobeniusNorm_smul]
      rw [abs_of_pos (inv_pos.mpr hnorm_pos)]
      field_simp [ne_of_gt hnorm_pos]
    have hUnitY :
        frobeniusNorm
            (tangentProjection S (samplingProjection Omega Y) - p • Y) ≤
          epsilon * p :=
      hUnit Y hYtangent (by simp [hYnorm])
    let F : ℝ :=
      frobeniusNorm
        (tangentProjection S (samplingProjection Omega X) - p • X)
    have hFluctY :
        tangentProjection S (samplingProjection Omega Y) - p • Y =
          (frobeniusNorm X)⁻¹ •
            (tangentProjection S (samplingProjection Omega X) - p • X) := by
      dsimp [Y]
      exact tangent_sampling_fluctuation_smul Omega S p (frobeniusNorm X)⁻¹ X
    have hNormFluctY :
        frobeniusNorm
            (tangentProjection S (samplingProjection Omega Y) - p • Y) =
          (frobeniusNorm X)⁻¹ * F := by
      rw [hFluctY, frobeniusNorm_smul]
      rw [abs_of_pos (inv_pos.mpr hnorm_pos)]
    have hNormalized : (frobeniusNorm X)⁻¹ * F ≤ epsilon * p := by
      simpa [hNormFluctY] using hUnitY
    have hmul := mul_le_mul_of_nonneg_left hNormalized hnorm_nonneg
    have hleft : frobeniusNorm X * ((frobeniusNorm X)⁻¹ * F) = F := by
      field_simp [ne_of_gt hnorm_pos]
    have hright : frobeniusNorm X * (epsilon * p) =
        epsilon * p * frobeniusNorm X := by
      ring
    simpa [TangentSamplingConcentration, F, hleft, hright] using hmul
