-- Prove2me | solution 1 for MeasureTheory.volume_smul_rpow_half
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:28:30.075429+00:00
-- url     : https://prove2.me/submissions/f82766df-b9d0-49e8-9bee-f9c610207ab2

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false

open scoped Pointwise
open MeasureTheory

theorem solution (S : Set (EuclideanSpace ℝ (Fin 2))) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal a * volume S ^ (2 : ℝ)⁻¹ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) ha]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow ha]
  simpa using ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) (ENNReal.ofReal a)
