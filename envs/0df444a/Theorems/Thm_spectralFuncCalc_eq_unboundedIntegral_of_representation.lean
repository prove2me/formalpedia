-- Prove2me | Theorems.Thm_spectralFuncCalc_eq_unboundedIntegral_of_representation
-- name    : spectralFuncCalc_eq_unboundedIntegral_of_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:11:16.874681+00:00
-- url     : https://prove2.me/theorems/1d13940f-37b2-4b21-9ffb-f597f2105ec7
-- title:
--   spectral Func Calc eq unbounded Integral of representation: spectral Func Calc eq unbounded Integral of representation
-- statement:
--   Every PVM representing a self-adjoint operator computes the selected spectral functional
--   calculus.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L379-L390
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L379-L390

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Spectral_FuncCalc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Definitions.Def_Spectral_Spectral_Uniqueness
set_option autoImplicit false
open Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectralFuncCalc_eq_unboundedIntegral_of_representation
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E_pvm : PVM E)
    (hE : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (f : ℝ → ℂ) (hf : Measurable f) :
    spectralFuncCalc A hA f hf = E_pvm.unboundedIntegral f hf := by sorry
