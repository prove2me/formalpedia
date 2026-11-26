-- Prove2me | Theorems.Thm_numericalRange_zero
-- name    : numericalRange_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:02.688701+00:00
-- url     : https://prove2.me/theorems/fb77c4d6-5946-4f1d-bf8d-7813d8840db8
-- title:
--   numerical Range zero: numerical Range zero
-- statement:
--   On a nontrivial space, the numerical range of the zero operator is the
--   singleton `{0}`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L57-L72
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L57-L72

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_zero [Nontrivial E] :
    numericalRange (0 : E →L[ℂ] E) = {0} := by sorry
