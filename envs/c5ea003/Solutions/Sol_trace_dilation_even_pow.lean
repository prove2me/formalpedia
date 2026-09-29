-- Prove2me | solution 1 for trace_dilation_even_pow
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:30:49.214431+00:00
-- url     : https://prove2.me/submissions/8c0407ce-fcea-47dc-b748-fe71e9867e6d

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Matrix
open scoped BigOperators

theorem solution {n1 n2 : ℕ} (S : Matrix (Fin n1) (Fin n2) ℝ) (n : ℕ) :
    Matrix.trace ((Matrix.fromBlocks 0 S Sᵀ 0) ^ (2 * n))
      = Matrix.trace ((S * Sᵀ) ^ n) + Matrix.trace ((Sᵀ * S) ^ n) := by
  classical
  -- ℋ^(2n) = blockdiag((S Sᵀ)^n, (Sᵀ S)^n)
  have dilation_sq : (Matrix.fromBlocks 0 S Sᵀ 0) ^ 2
      = Matrix.fromBlocks (S * Sᵀ) 0 0 (Sᵀ * S) := by
    rw [pow_two, Matrix.fromBlocks_multiply]
    simp
  have dilation_even_pow : ∀ k : ℕ, (Matrix.fromBlocks 0 S Sᵀ 0) ^ (2 * k)
      = Matrix.fromBlocks ((S * Sᵀ) ^ k) 0 0 ((Sᵀ * S) ^ k) := by
    intro k
    induction k with
    | zero => simp [Matrix.fromBlocks_one]
    | succ j ih =>
        have h2 : 2 * (j + 1) = 2 * j + 2 := by ring
        rw [h2, pow_add, ih, dilation_sq, Matrix.fromBlocks_multiply]
        simp [pow_succ]
  -- trace of a block matrix = trace TL + trace BR
  have trace_fromBlocks : ∀ (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n1) (Fin n2) ℝ)
      (C : Matrix (Fin n2) (Fin n1) ℝ) (D : Matrix (Fin n2) (Fin n2) ℝ),
      Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
    intro A B C D
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Fintype.sum_sum_type]
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  rw [dilation_even_pow, trace_fromBlocks]
