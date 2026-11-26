-- Prove2me | Theorems.Thm_re_inner_mul_lower_iff_norm_adjoint_sub_sq_le
-- name    : re_inner_mul_lower_iff_norm_adjoint_sub_sq_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:48.566488+00:00
-- url     : https://prove2.me/theorems/951131be-800e-5b2b-bb45-21140c9244ca
-- title:
--   re inner mul lower iff norm adjoint sub sq le: re inner mul lower iff norm adjoint sub sq le
-- statement:
--   The one-sided product estimate used in the Palencia balance is exactly a
--   relative bound on the antisymmetric auxiliary component.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L683-L688
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L683-L688

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem re_inner_mul_lower_iff_norm_adjoint_sub_sq_le
    (F G : E →L[ℂ] E) (x : E) (m : ℝ) :
    -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ ↔
      ‖(star F - G) x‖ ^ 2 ≤ ‖(star F + G) x‖ ^ 2 + 4 * m ^ 2 := by sorry
