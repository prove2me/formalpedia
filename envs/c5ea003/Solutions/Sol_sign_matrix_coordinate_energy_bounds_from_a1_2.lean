-- Prove2me | solution 2 for sign_matrix_coordinate_energy_bounds_from_a1
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-23T17:27:32.082444+00:00
-- url     : https://prove2.me/submissions/f975d438-ebcc-49b0-a878-14566ffdbd73

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₁ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₁ → A1 S μ₁ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ)) := by
  intro n₁ n₂ r M μ₁ S hn₁ hn₂ hr hμ₁ hA1
  constructor
  · intro i
    have hv : ∀ k l : Fin r, ∑ j : Fin n₂, S.v k j * S.v l j = if k = l then 1 else 0 := S.v_orthonormal
    have eq1 : ∑ j : Fin n₂, (∑ k : Fin r, S.u k i * S.v k j) ^ 2 = ∑ k : Fin r, (S.u k i) ^ 2 := by
      calc
        ∑ j : Fin n₂, (∑ k : Fin r, S.u k i * S.v k j) ^ 2
          = ∑ j : Fin n₂, (∑ k : Fin r, S.u k i * S.v k j) * (∑ l : Fin r, S.u l i * S.v l j) := by simp_rw [sq]
        _ = ∑ j : Fin n₂, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v k j) * (S.u l i * S.v l j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
        _ = ∑ k : Fin r, ∑ l : Fin r, ∑ j : Fin n₂, (S.u k i * S.v k j) * (S.u l i * S.v l j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_comm]
        _ = ∑ k : Fin r, ∑ l : Fin r, ∑ j : Fin n₂, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u l i) * (∑ j : Fin n₂, S.v k j * S.v l j) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u l i) * (if k = l then 1 else 0) := by
          simp_rw [hv]
        _ = ∑ k : Fin r, ∑ l : Fin r, if k = l then S.u k i * S.u l i else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          split_ifs with h
          · ring
          · ring
        _ = ∑ k : Fin r, S.u k i * S.u k i := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_ite_eq]
          simp [hk]
        _ = ∑ k : Fin r, (S.u k i) ^ 2 := by simp_rw [sq]
    have eq2 : ∑ j : Fin n₂, (∑ k : Fin r, S.u k i * S.v k j) ^ 2 ≤ ∑ j : Fin n₂, (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hA1ij : |signMatrix S i j| ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := hA1 i j
      have hSign : signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
        dsimp [signMatrix]
        rw [Matrix.sum_apply]
        rfl
      rw [← hSign]
      have hA1ij_sq : |signMatrix S i j| ^ 2 ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 := by
        gcongr
      have hAbs : |signMatrix S i j| ^ 2 = (signMatrix S i j) ^ 2 := sq_abs _
      rwa [hAbs] at hA1ij_sq
    have eq3 : ∑ j : Fin n₂, (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 = μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ) := by
      have hSqrt : (Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 = (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
        apply Real.sq_sqrt
        positivity
      simp_rw [mul_pow, hSqrt]
      have hSum : ∑ j : Fin n₂, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = (n₂ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hSum]
      have hn2_ne_zero : (n₂ : ℝ) ≠ 0 := by positivity
      calc
        (n₂ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
          = (n₂ : ℝ) * (μ₁ ^ 2 * (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by ring
        _ = μ₁ ^ 2 * (r : ℝ) * (n₂ : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by ring
        _ = μ₁ ^ 2 * (r : ℝ) / (n₁ : ℝ) := by
          rw [mul_div_mul_right _ _ hn2_ne_zero]
    rwa [eq1, eq3] at eq2
  · intro j
    have hu : ∀ k l : Fin r, ∑ i : Fin n₁, S.u k i * S.u l i = if k = l then 1 else 0 := S.u_orthonormal
    have eq1 : ∑ i : Fin n₁, (∑ k : Fin r, S.v k j * S.u k i) ^ 2 = ∑ k : Fin r, (S.v k j) ^ 2 := by
      calc
        ∑ i : Fin n₁, (∑ k : Fin r, S.v k j * S.u k i) ^ 2
          = ∑ i : Fin n₁, (∑ k : Fin r, S.v k j * S.u k i) * (∑ l : Fin r, S.v l j * S.u l i) := by simp_rw [sq]
        _ = ∑ i : Fin n₁, ∑ k : Fin r, ∑ l : Fin r, (S.v k j * S.u k i) * (S.v l j * S.u l i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
        _ = ∑ k : Fin r, ∑ l : Fin r, ∑ i : Fin n₁, (S.v k j * S.u k i) * (S.v l j * S.u l i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_comm]
        _ = ∑ k : Fin r, ∑ l : Fin r, ∑ i : Fin n₁, (S.v k j * S.v l j) * (S.u k i * S.u l i) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ k : Fin r, ∑ l : Fin r, (S.v k j * S.v l j) * (∑ i : Fin n₁, S.u k i * S.u l i) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ k : Fin r, ∑ l : Fin r, (S.v k j * S.v l j) * (if k = l then 1 else 0) := by
          simp_rw [hu]
        _ = ∑ k : Fin r, ∑ l : Fin r, if k = l then S.v k j * S.v l j else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          split_ifs with h
          · ring
          · ring
        _ = ∑ k : Fin r, S.v k j * S.v k j := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_ite_eq]
          simp [hk]
        _ = ∑ k : Fin r, (S.v k j) ^ 2 := by simp_rw [sq]
    have eq2 : ∑ i : Fin n₁, (∑ k : Fin r, S.v k j * S.u k i) ^ 2 ≤ ∑ i : Fin n₁, (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hA1ij : |signMatrix S i j| ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := hA1 i j
      have hSign : signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
        dsimp [signMatrix]
        rw [Matrix.sum_apply]
        rfl
      have hComm : ∑ k : Fin r, S.v k j * S.u k i = ∑ k : Fin r, S.u k i * S.v k j := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hComm, ← hSign]
      have hA1ij_sq : |signMatrix S i j| ^ 2 ≤ (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 := by
        gcongr
      have hAbs : |signMatrix S i j| ^ 2 = (signMatrix S i j) ^ 2 := sq_abs _
      rwa [hAbs] at hA1ij_sq
    have eq3 : ∑ i : Fin n₁, (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 = μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) := by
      have hSqrt : (Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2 = (r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by
        apply Real.sq_sqrt
        positivity
      simp_rw [mul_pow, hSqrt]
      have hSum : ∑ i : Fin n₁, μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = (n₁ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hSum]
      have hn1_ne_zero : (n₁ : ℝ) ≠ 0 := by positivity
      calc
        (n₁ : ℝ) * (μ₁ ^ 2 * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
          = μ₁ ^ 2 * (r : ℝ) * (n₁ : ℝ) / ((n₂ : ℝ) * (n₁ : ℝ)) := by ring
        _ = μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) := by
          rw [mul_div_mul_right _ _ hn1_ne_zero]
    have eq_final : ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₁ ^ 2 * (r : ℝ) / (n₂ : ℝ) := by
      rwa [eq1, eq3] at eq2
    exact eq_final
