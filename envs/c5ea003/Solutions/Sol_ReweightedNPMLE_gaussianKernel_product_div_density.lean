-- Prove2me | solution 1 for ReweightedNPMLE.gaussianKernel_product_div_density
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:23.863056+00:00
-- url     : https://prove2.me/submissions/fe5bc916-72d2-4163-8287-b171d59b7c7d

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Pointwise completed-square identity behind the Gaussian-mixture
weighted `L²` calculation. -/
theorem solution {d : ℕ} (x θ η : Point d) :
    gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) * gaussianDensity d (x - (θ + η)) := by
  rw [gaussianKernel_eq_density_mul_exp_score,
    gaussianKernel_eq_density_mul_exp_score]
  have hd : gaussianDensity d x ≠ 0 := (gaussianDensity_pos d x).ne'
  field_simp
  unfold gaussianDensity gaussianScore
  calc
    gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2) *
          Real.exp (inner ℝ x θ - ‖θ‖ ^ 2 / 2) *
          Real.exp (inner ℝ x η - ‖η‖ ^ 2 / 2) =
        gaussianConstant d * Real.exp
          ((-‖x‖ ^ 2 / 2) + (inner ℝ x θ - ‖θ‖ ^ 2 / 2) +
            (inner ℝ x η - ‖η‖ ^ 2 / 2)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = gaussianConstant d * Real.exp
          (inner ℝ θ η + (-‖x - (θ + η)‖ ^ 2 / 2)) := by
      congr 2
      rw [norm_sub_sq_real, norm_add_sq_real, real_inner_comm η θ, inner_add_right]
      ring
    _ = Real.exp (inner ℝ θ η) *
          (gaussianConstant d * Real.exp (-‖x - (θ + η)‖ ^ 2 / 2)) := by
      rw [Real.exp_add]
      ring
