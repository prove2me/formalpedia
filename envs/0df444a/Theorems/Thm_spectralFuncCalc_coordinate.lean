-- Prove2me | Theorems.Thm_spectralFuncCalc_coordinate
-- name    : spectralFuncCalc_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:13.674862+00:00
-- url     : https://prove2.me/theorems/a9b7d7ed-0d01-54a3-9d61-db6138686acf
-- title:
--   spectral Func Calc coordinate: spectral Func Calc coordinate
-- statement:
--   Applying the spectral functional calculus to the coordinate function recovers `A`.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/FuncCalc.lean#L28-L33
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/FuncCalc.lean#L28-L33

import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_FuncCalc
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectralFuncCalc_coordinate
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    spectralFuncCalc A hA ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by sorry
