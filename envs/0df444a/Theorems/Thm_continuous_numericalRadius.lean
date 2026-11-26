-- Prove2me | Theorems.Thm_continuous_numericalRadius
-- name    : continuous_numericalRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:55:45.707598+00:00
-- url     : https://prove2.me/theorems/50026504-de8e-5120-bae2-987c099dc2cd
-- title:
--   continuous numerical Radius: continuous numerical Radius
-- statement:
--   Numerical radius is continuous in the operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L301-L303
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L301-L303

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_numericalRadius :
    Continuous (numericalRadius : (E →L[ℂ] E) → ℝ) := by sorry
