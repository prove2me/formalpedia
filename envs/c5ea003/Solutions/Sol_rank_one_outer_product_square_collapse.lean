-- Prove2me | solution 1 for rank_one_outer_product_square_collapse
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:51.984783+00:00
-- url     : https://prove2.me/submissions/91bf0f62-6f4d-436e-9279-46197fc69472

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} (y : Fin d → ℝ) :
    Matrix.vecMulVec y y * Matrix.vecMulVec y y
      = (y ⬝ᵥ y) • Matrix.vecMulVec y y := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring
