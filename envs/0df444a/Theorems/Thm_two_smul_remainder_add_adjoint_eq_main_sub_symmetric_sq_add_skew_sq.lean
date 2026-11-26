-- Prove2me | Theorems.Thm_two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq
-- name    : two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:35:46.422417+00:00
-- url     : https://prove2.me/theorems/9c432f69-9155-584e-874b-9d470c700fd7
-- title:
--   two smul remainder add adjoint eq main sub symmetric sq add skew sq: two smul remainder add adjoint eq main sub symmetric sq add skew sq
-- statement:
--   If an auxiliary product is separated as `F G = H - Q`, then twice the
--   Hermitian remainder is exactly twice the Hermitian main term, minus the
--   symmetric square, plus the antisymmetric square.  Thus positivity of the
--   double-layer/Kadison part and control of the skew part are distinct pieces;
--   no triangle inequality or commutation hypothesis enters this identity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L668-L679
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L668-L679

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem two_smul_remainder_add_adjoint_eq_main_sub_symmetric_sq_add_skew_sq
    (F G H Q : E →L[ℂ] E) (hdecomp : F * G = H - Q) :
    (2 : ℂ) • (Q + star Q) =
      (2 : ℂ) • (H + star H) -
        (F + star G) * (star F + G) +
        (F - star G) * (star F - G) := by sorry
