-- Prove2me | Theorems.Thm_numericalRange_scalar
-- name    : numericalRange_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:09.768544+00:00
-- url     : https://prove2.me/theorems/50feaea9-27cd-4526-9201-e8a570f56d39
-- title:
--   numerical Range scalar: numerical Range scalar
-- statement:
--   On a nontrivial space, a scalar operator has singleton numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L75-L78
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L75-L78

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_scalar [Nontrivial E] (c : ℂ) :
    numericalRange (c • (1 : E →L[ℂ] E)) = {c} := by sorry
