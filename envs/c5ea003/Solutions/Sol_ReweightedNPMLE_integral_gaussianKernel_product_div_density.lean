-- Prove2me | solution 1 for ReweightedNPMLE.integral_gaussianKernel_product_div_density
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:02.477637+00:00
-- url     : https://prove2.me/submissions/0095dad4-d060-4202-936f-e5deda2381f2

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density

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
/-- Exact Gaussian overlap identity used to turn moment matching into a
global weighted `L²`, hence Hellinger, approximation. -/
theorem solution {d : ℕ} (θ η : Point d) :
    ∫ x : Point d,
        gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) := by
  calc
    (∫ x : Point d,
        gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x) =
        ∫ x : Point d,
          Real.exp (inner ℝ θ η) * gaussianDensity d (x - (θ + η)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        gaussianKernel_product_div_density x θ η
    _ = Real.exp (inner ℝ θ η) *
        ∫ x : Point d, gaussianDensity d (x - (θ + η)) := by
      rw [integral_const_mul]
    _ = Real.exp (inner ℝ θ η) := by
      rw [integral_sub_right_eq_self, integral_gaussianDensity, mul_one]
