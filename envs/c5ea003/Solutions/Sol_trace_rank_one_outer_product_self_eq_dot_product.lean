-- Prove2me | solution 1 for trace_rank_one_outer_product_self_eq_dot_product
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:58.732173+00:00
-- url     : https://prove2.me/submissions/15367dff-f5b9-48fa-bd61-7ea29e683ee0

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y : Fin d → ℝ) :
    Matrix.trace (Matrix.vecMulVec y y) = y ⬝ᵥ y := by
  unfold Matrix.trace Matrix.vecMulVec dotProduct
  simp [Matrix.diag]
