-- Prove2me | Theorems.Thm_four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub
-- name    : four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:46.680075+00:00
-- url     : https://prove2.me/theorems/cfef5454-bd29-4e3d-b656-a38a2f2c6580
-- title:
--   four mul re inner mul eq norm adjoint add sq sub: four mul re inner mul eq norm adjoint add sq sub
-- statement:
--   The Hermitian part of an auxiliary product is exactly the difference
--   between the squared symmetric and antisymmetric components.  This is the
--   operator-vector form of the polarization identity
--   `4 Re(FG) = (F† + G)†(F† + G) - (F† - G)†(F† - G)`; it requires no
--   commutation hypothesis.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L644-L661
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L644-L661

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem four_mul_re_inner_mul_eq_norm_adjoint_add_sq_sub
    (F G : E →L[ℂ] E) (x : E) :
    4 * RCLike.re ⟪x, (F * G) x⟫_ℂ =
      ‖(star F + G) x‖ ^ 2 - ‖(star F - G) x‖ ^ 2 := by sorry
