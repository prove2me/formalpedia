-- Prove2me | Theorems.Thm_numericalRange_smul_sub_smul_one
-- name    : numericalRange_smul_sub_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:10.854557+00:00
-- url     : https://prove2.me/theorems/dbdb114b-3b48-5562-9d42-49e81d25d24f
-- title:
--   numerical Range smul sub smul one: numerical Range smul sub smul one
-- statement:
--   The numerical range commutes with the affine normalization
--   `A ↦ c • (A - z₀ I)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L19-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Affine.lean#L19-L31

import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_NumericalRange_Affine
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_smul_sub_smul_one
    (A : E →L[ℂ] E) (c z₀ : ℂ) :
    numericalRange (c • (A - z₀ • 1)) =
      (fun z => c * (z - z₀)) '' numericalRange A := by sorry
