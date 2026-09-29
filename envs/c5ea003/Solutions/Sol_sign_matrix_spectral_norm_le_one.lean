-- Prove2me | solution 1 for sign_matrix_spectral_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T03:19:59.427747+00:00
-- url     : https://prove2.me/submissions/71cf4c7c-5342-447f-b355-4a4d15ebd374

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

open scoped Classical BigOperators Matrix

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    spectralNorm (signMatrix S) ≤ 1 := by
  set E := signMatrix S with hE
  have hEntry : ∀ i j, E i j = ∑ k, S.u k i * S.v k j := by
    intro i j
    simp only [hE, signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
  -- (E *ᵥ x) i = ∑ k, u_k i * c_k  where c_k = ∑ j, v_k j * x_j
  have hmulVec : ∀ (x : Fin n₂ → ℝ) (i : Fin n₁),
      (E *ᵥ x) i = ∑ k, S.u k i * (∑ j, S.v k j * x j) := by
    intro x i
    show (fun j => E i j) ⬝ᵥ x = _
    rw [dotProduct]
    calc ∑ j, E i j * x j
        = ∑ j, ∑ k, (S.u k i * S.v k j) * x j := by
          apply Finset.sum_congr rfl; intro j _; rw [hEntry, Finset.sum_mul]
      _ = ∑ k, ∑ j, (S.u k i * S.v k j) * x j := Finset.sum_comm
      _ = ∑ k, S.u k i * (∑ j, S.v k j * x j) := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  -- Squared norm of toEuclideanLin E applied to a Euclidean vector
  have hnormSq : ∀ (x : EuclideanSpace ℝ (Fin n₂)),
      ‖Matrix.toEuclideanLin E x‖ ^ 2
        = ∑ k, (∑ j, S.v k j * x j) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    have hcoord : ∀ i, (Matrix.toEuclideanLin E x) i = (E *ᵥ (⇑x)) i := by
      intro i
      rfl
    set c : Fin r → ℝ := fun k => ∑ j, S.v k j * x j with hc
    calc ∑ i, (Matrix.toEuclideanLin E x) i ^ 2
        = ∑ i, (∑ k, S.u k i * c k) ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          rw [hcoord, hmulVec]
      _ = ∑ i, ∑ k, ∑ l, (S.u k i * c k) * (S.u l i * c l) := by
          apply Finset.sum_congr rfl; intro i _
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ k, ∑ l, ∑ i, (S.u k i * c k) * (S.u l i * c l) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_comm]
      _ = ∑ k, ∑ l, (c k * c l) * (∑ i, S.u k i * S.u l i) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ k, ∑ l, (c k * c l) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [S.u_orthonormal]
      _ = ∑ k, c k ^ 2 := by
          apply Finset.sum_congr rfl; intro k _
          rw [show (∑ l, c k * c l * if k = l then (1:ℝ) else 0)
                = ∑ l, (if k = l then c k * c l else 0) by
            apply Finset.sum_congr rfl; intro l _; split <;> ring]
          rw [Finset.sum_ite_eq Finset.univ k (fun l => c k * c l)]
          simp [sq]
  -- Bessel inequality: ∑ k, c_k² ≤ ∑ j, x_j²  with c_k = ∑ j, v_k j x_j
  have hBessel : ∀ (x : Fin n₂ → ℝ),
      (∑ k, (∑ j, S.v k j * x j) ^ 2) ≤ ∑ j, (x j) ^ 2 := by
    intro x
    set c : Fin r → ℝ := fun k => ∑ j, S.v k j * x j with hc
    -- expand 0 ≤ ∑ j (x_j - ∑_k c_k v_k j)²
    have hnn : (0:ℝ) ≤ ∑ j, (x j - ∑ k, c k * S.v k j) ^ 2 := by
      apply Finset.sum_nonneg; intro j _; positivity
    -- last term: ∑ j (∑ k c_k v_k j)² = ∑ k c_k²
    have hlast : (∑ j, (∑ k, c k * S.v k j) ^ 2) = ∑ k, c k ^ 2 := by
      calc ∑ j, (∑ k, c k * S.v k j) ^ 2
          = ∑ j, ∑ k, ∑ l, (c k * S.v k j) * (c l * S.v l j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [sq, Finset.sum_mul_sum]
        _ = ∑ k, ∑ l, ∑ j, (c k * S.v k j) * (c l * S.v l j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_comm]
        _ = ∑ k, ∑ l, (c k * c l) * (∑ j, S.v k j * S.v l j) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro l _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ k, ∑ l, (c k * c l) * (if k = l then 1 else 0) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro l _
            rw [S.v_orthonormal]
        _ = ∑ k, c k ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [show (∑ l, c k * c l * if k = l then (1:ℝ) else 0)
                  = ∑ l, (if k = l then c k * c l else 0) by
              apply Finset.sum_congr rfl; intro l _; split <;> ring]
            rw [Finset.sum_ite_eq Finset.univ k (fun l => c k * c l)]
            simp [sq]
    -- cross term: ∑ j x_j (∑ k c_k v_k j) = ∑ k c_k²
    have hcross : (∑ j, x j * (∑ k, c k * S.v k j)) = ∑ k, c k ^ 2 := by
      calc ∑ j, x j * (∑ k, c k * S.v k j)
          = ∑ j, ∑ k, c k * (S.v k j * x j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        _ = ∑ k, c k * (∑ j, S.v k j * x j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
        _ = ∑ k, c k ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [hc]; simp only; rw [sq]
    -- expand the square sum
    have hexpand : (∑ j, (x j - ∑ k, c k * S.v k j) ^ 2)
        = (∑ j, (x j) ^ 2) - 2 * (∑ k, c k ^ 2) + (∑ k, c k ^ 2) := by
      have : (∑ j, (x j - ∑ k, c k * S.v k j) ^ 2)
          = ∑ j, ((x j)^2 - 2 * (x j * (∑ k, c k * S.v k j))
              + (∑ k, c k * S.v k j) ^ 2) := by
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hcross, hlast]
    rw [hexpand] at hnn
    linarith
  -- Combine: ‖toEuclideanLin E x‖ ≤ ‖x‖ for all Euclidean x
  have hbound : ∀ (x : EuclideanSpace ℝ (Fin n₂)),
      ‖Matrix.toEuclideanLin E x‖ ≤ 1 * ‖x‖ := by
    intro x
    rw [one_mul]
    have hsq : ‖Matrix.toEuclideanLin E x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hnormSq x, EuclideanSpace.real_norm_sq_eq]
      exact hBessel (⇑x)
    have h1 : (0:ℝ) ≤ ‖Matrix.toEuclideanLin E x‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
    nlinarith [hsq, h1, h2]
  -- Conclude on the spectral norm
  show ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin E)‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [LinearMap.coe_toContinuousLinearMap']
  exact hbound x
