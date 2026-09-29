-- Prove2me | solution 1 for sign_matrix_frobenius_norm_le_sqrt_rank
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:29:59.812582+00:00
-- url     : https://prove2.me/submissions/377f2439-fc06-4e11-a959-bee5ad708e39

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ) := by
  have hsq : frobeniusNormSq (signMatrix S) = (r : ℝ) := by
    unfold frobeniusNormSq signMatrix
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
    have hbody : ∀ i : Fin n₁, ∀ j : Fin n₂,
        (∑ k, S.u k i * S.v k j) ^ 2
          = ∑ k, ∑ l, (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
      intro i j
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    simp only [hbody]
    rw [Finset.sum_congr rfl (fun (i : Fin n₁) _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun (k : Fin r) _ =>
          Finset.sum_congr rfl (fun (i : Fin n₁) _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun (k : Fin r) _ => Finset.sum_comm)]
    have hfac : ∀ k l : Fin r,
        (∑ i, ∑ j, (S.u k i * S.u l i) * (S.v k j * S.v l j))
          = (∑ i, S.u k i * S.u l i) * (∑ j, S.v k j * S.v l j) := by
      intro k l
      rw [Finset.sum_mul_sum]
    simp only [hfac, S.u_orthonormal, S.v_orthonormal]
    simp
  have heq : frobeniusNorm (signMatrix S) = Real.sqrt (r : ℝ) := by
    unfold frobeniusNorm; rw [hsq]
  exact le_of_eq heq
