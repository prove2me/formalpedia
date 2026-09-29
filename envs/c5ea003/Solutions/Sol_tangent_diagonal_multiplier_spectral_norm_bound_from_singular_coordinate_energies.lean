-- Prove2me | solution 1 for tangent_diagonal_multiplier_spectral_norm_bound_from_singular_coordinate_energies
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T17:37:46.561116+00:00
-- url     : https://prove2.me/submissions/b1886f00-fd10-46a5-8608-c8b1479c2f58

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

open scoped Classical BigOperators Matrix.Norms.L2Operator

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma leftSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.u k i) ^ 2 := by
  unfold leftSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma rightSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.v k j) ^ 2 := by
  unfold rightSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single j]
  · simp [pow_two]
  · intro b _hb hb
    simp [hb]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private lemma twoSidedSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) i j =
      (∑ k : Fin r, (S.u k i) ^ 2) *
        (∑ k : Fin r, (S.v k j) ^ 2) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [pow_two, Finset.mul_sum, Finset.sum_mul]
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection, leftSingularProjection_coordinate_same,
    rightSingularProjection_coordinate_same,
    twoSidedSingularProjection_coordinate_same]

private lemma diagonal_multiplier_matrix_identity
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentDiagonalMultiplier S X =
      Matrix.diagonal (fun i : Fin n₁ => ∑ k : Fin r, (S.u k i) ^ 2) *
          X *
          Matrix.diagonal
            (fun j : Fin n₂ => 1 - ∑ k : Fin r, (S.v k j) ^ 2) +
        X * Matrix.diagonal
          (fun j : Fin n₂ => ∑ k : Fin r, (S.v k j) ^ 2) := by
  ext i j
  rw [tangentDiagonalMultiplier, tangent_coordinate_kernel_diagonal_formula]
  simp only [Matrix.add_apply]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private lemma diagonal_l2_opNorm_le_of_abs_le
    {n : ℕ} (d : Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ i, |d i| ≤ a) :
    ‖(Matrix.diagonal d : Matrix (Fin n) (Fin n) ℝ)‖ ≤ a := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg ha).2 hd

private lemma diagonal_l2_opNorm_le_of_nonneg_le
    {n : ℕ} (d : Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hd_nonneg : ∀ i, 0 ≤ d i) (hd_le : ∀ i, d i ≤ a) :
    ‖(Matrix.diagonal d : Matrix (Fin n) (Fin n) ℝ)‖ ≤ a := by
  exact diagonal_l2_opNorm_le_of_abs_le d ha fun i =>
    by simpa [abs_of_nonneg (hd_nonneg i)] using hd_le i

private lemma diagonal_one_sub_l2_opNorm_le_one
    {n : ℕ} (d : Fin n → ℝ)
    (hd_nonneg : ∀ i, 0 ≤ d i) (hd_one : ∀ i, d i ≤ 1) :
    ‖(Matrix.diagonal (fun i => 1 - d i) :
        Matrix (Fin n) (Fin n) ℝ)‖ ≤ (1 : ℝ) := by
  exact diagonal_l2_opNorm_le_of_abs_le (fun i => 1 - d i) zero_le_one fun i => by
    have hnonneg : 0 ≤ 1 - d i := by linarith [hd_one i]
    have hle : 1 - d i ≤ 1 := by linarith [hd_nonneg i]
    simpa [abs_of_nonneg hnonneg] using hle

/-- Source: Candes-Recht 2008, PDF p. 27, Lemma 6.4, equations
(6.10)--(6.11).  The proof formalizes the identity
`D_T(X)=Λ_U X(I-Λ_V)+XΛ_V` and applies the L2 operator-norm product bound. -/
theorem solution :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        spectralNorm (tangentDiagonalMultiplier S X) ≤
          Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm X := by
  refine ⟨2, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S X hn₁ hn₂ hr hμ₀ hu hv huOne hvOne
  let U : Fin n₁ → ℝ := fun i => ∑ k : Fin r, (S.u k i) ^ 2
  let V : Fin n₂ → ℝ := fun j => ∑ k : Fin r, (S.v k j) ^ 2
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hU_nonneg : ∀ i, 0 ≤ U i := by
    intro i
    dsimp [U]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hV_nonneg : ∀ j, 0 ≤ V j := by
    intro j
    dsimp [V]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hU_one : ∀ i, U i ≤ 1 := by
    intro i
    simpa [U] using huOne i
  have hV_one : ∀ j, V j ≤ 1 := by
    intro j
    simpa [V] using hvOne j
  have hU_scale : ∀ i, U i ≤ scale := by
    intro i
    have hmono :
        μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
      exact_mod_cast min_le_left n₁ n₂
    exact le_trans (by simpa [U] using hu i) hmono
  have hV_scale : ∀ j, V j ≤ scale := by
    intro j
    have hmono :
        μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
      exact_mod_cast min_le_right n₁ n₂
    exact le_trans (by simpa [V] using hv j) hmono
  have hU_norm :
      ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ)‖ ≤ scale :=
    diagonal_l2_opNorm_le_of_nonneg_le U hscale_nonneg hU_nonneg hU_scale
  have hV_norm :
      ‖(Matrix.diagonal V : Matrix (Fin n₂) (Fin n₂) ℝ)‖ ≤ scale :=
    diagonal_l2_opNorm_le_of_nonneg_le V hscale_nonneg hV_nonneg hV_scale
  have hIminusV :
      ‖(Matrix.diagonal (fun j : Fin n₂ => 1 - V j) :
          Matrix (Fin n₂) (Fin n₂) ℝ)‖ ≤ (1 : ℝ) :=
    diagonal_one_sub_l2_opNorm_le_one V hV_nonneg hV_one
  have hmul_left :
      ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X *
          Matrix.diagonal (fun j : Fin n₂ => 1 - V j)‖ ≤
        scale * ‖X‖ := by
    have h1 := Matrix.l2_opNorm_mul
      ((Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X)
      (Matrix.diagonal (fun j : Fin n₂ => 1 - V j))
    have h0 := Matrix.l2_opNorm_mul
      (Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) X
    calc
      ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X *
          Matrix.diagonal (fun j : Fin n₂ => 1 - V j)‖
          ≤ ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X‖ *
              ‖(Matrix.diagonal (fun j : Fin n₂ => 1 - V j) :
                  Matrix (Fin n₂) (Fin n₂) ℝ)‖ := h1
      _ ≤ (‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ)‖ * ‖X‖) * 1 := by
          gcongr
      _ ≤ (scale * ‖X‖) * 1 := by
          gcongr
      _ = scale * ‖X‖ := by ring
  have hmul_right :
      ‖X * Matrix.diagonal V‖ ≤ scale * ‖X‖ := by
    have h0 := Matrix.l2_opNorm_mul X
      (Matrix.diagonal V : Matrix (Fin n₂) (Fin n₂) ℝ)
    calc
      ‖X * Matrix.diagonal V‖
          ≤ ‖X‖ * ‖(Matrix.diagonal V : Matrix (Fin n₂) (Fin n₂) ℝ)‖ := h0
      _ ≤ ‖X‖ * scale := by
          gcongr
      _ = scale * ‖X‖ := by ring
  have hadd :
      ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X *
          Matrix.diagonal (fun j : Fin n₂ => 1 - V j) +
        X * Matrix.diagonal V‖ ≤
          scale * ‖X‖ + scale * ‖X‖ :=
    (norm_add_le_of_le hmul_left hmul_right)
  have hidentity := diagonal_multiplier_matrix_identity S X
  calc
    spectralNorm (tangentDiagonalMultiplier S X)
        = ‖tangentDiagonalMultiplier S X‖ := spectralNorm_eq_l2_opNorm _
    _ = ‖(Matrix.diagonal U : Matrix (Fin n₁) (Fin n₁) ℝ) * X *
          Matrix.diagonal (fun j : Fin n₂ => 1 - V j) +
        X * Matrix.diagonal V‖ := by
          rw [hidentity]
    _ ≤ scale * ‖X‖ + scale * ‖X‖ := hadd
    _ = 2 * scale * ‖X‖ := by ring
    _ = 2 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * spectralNorm X := by
      rw [spectralNorm_eq_l2_opNorm X]
