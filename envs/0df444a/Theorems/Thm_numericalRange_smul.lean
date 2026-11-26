-- Prove2me | Theorems.Thm_numericalRange_smul
-- name    : numericalRange_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:22:05.754748+00:00
-- url     : https://prove2.me/theorems/3903339c-6115-45f1-b92d-e82360046a32
-- title:
--   numerical Range smul: numerical Range smul
-- statement:
--   Scalar multiplication of an operator multiplies its numerical range by
--   the same scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L35-L39
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L35-L39

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_smul (A : E →L[ℂ] E) (c : ℂ) :
    numericalRange (c • A) =
      (fun z => c * z) '' numericalRange A := by sorry
