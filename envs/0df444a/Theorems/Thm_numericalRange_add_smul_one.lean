-- Prove2me | Theorems.Thm_numericalRange_add_smul_one
-- name    : numericalRange_add_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:26.222576+00:00
-- url     : https://prove2.me/theorems/08c7fa22-0f9b-4875-89b9-9d6ceb73dc59
-- title:
--   numerical Range add smul one: numerical Range add smul one
-- statement:
--   Adding a scalar operator translates the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L49-L53
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L49-L53

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_add_smul_one (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (A + c • 1) =
      (fun z => z + c) '' numericalRange A := by sorry
