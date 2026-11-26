-- Prove2me | Theorems.Thm_isCompact_numericalRange
-- name    : isCompact_numericalRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:07.190253+00:00
-- url     : https://prove2.me/theorems/bf5cea5c-cca8-5166-873e-d13ad5b83724
-- title:
--   is Compact numerical Range: is Compact numerical Range
-- statement:
--   In finite dimension the numerical range is compact: the continuous image of the unit sphere.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L31-L35
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L31-L35

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isCompact_numericalRange [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsCompact (numericalRange A) := by sorry
