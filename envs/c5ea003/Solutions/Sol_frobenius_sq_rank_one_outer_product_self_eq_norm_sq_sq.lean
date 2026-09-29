-- Prove2me | solution 1 for frobenius_sq_rank_one_outer_product_self_eq_norm_sq_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:26:00.057386+00:00
-- url     : https://prove2.me/submissions/56d9efbd-9da7-4e21-ab07-7d3af9e5e2fd

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y : Fin d → ℝ) :
    ∑ i, ∑ j, (Matrix.vecMulVec y y i j) ^ 2 = (∑ i, (y i) ^ 2) ^ 2 := by
  have hrow : ∀ i, ∑ j, (Matrix.vecMulVec y y i j) ^ 2 = (y i) ^ 2 * ∑ j, (y j) ^ 2 := by
    intro i
    simp only [Matrix.vecMulVec, Matrix.of_apply, mul_pow]
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hrow i), ← Finset.sum_mul, sq]
