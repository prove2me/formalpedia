-- Prove2me | Theorems.Thm_isClosed_numericalRange
-- name    : isClosed_numericalRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:14:20.182633+00:00
-- url     : https://prove2.me/theorems/20945dbd-9684-5353-97c2-0afbc1441d16
-- title:
--   is Closed numerical Range: is Closed numerical Range
-- statement:
--   In finite dimension the numerical range is closed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L38-L40
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L38-L40

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isClosed_numericalRange [FiniteDimensional ℂ E] (A : E →L[ℂ] E) :
    IsClosed (numericalRange A) := by sorry
