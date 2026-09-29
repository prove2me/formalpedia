-- Prove2me | solution 1 for sum_rank_one_outer_product_square_collapse
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:25:53.377771+00:00
-- url     : https://prove2.me/submissions/9f0fdb86-8107-46fe-9ddf-891f720631cd

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

theorem solution {d : ℕ} {ι : Type*} (s : Finset ι) (y : ι → Fin d → ℝ) :
    ∑ c ∈ s, (Matrix.vecMulVec (y c) (y c) * Matrix.vecMulVec (y c) (y c))
      = ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c) := by
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring
