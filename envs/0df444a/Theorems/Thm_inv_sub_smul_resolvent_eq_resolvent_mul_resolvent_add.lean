-- Prove2me | Theorems.Thm_inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
-- name    : inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:17.211812+00:00
-- url     : https://prove2.me/theorems/dd3898db-a2aa-5e09-b8a5-ce667f810e56
-- title:
--   inv sub smul resolvent eq resolvent mul resolvent add: inv sub smul resolvent eq resolvent mul resolvent add
-- statement:
--   The two-parameter resolvent identity in the form adapted to the nested
--   Cauchy kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L27-L61
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L27-L61

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]

theorem inv_sub_smul_resolvent_eq_resolvent_mul_resolvent_add
    (A : E →L[ℂ] E) {z sigma : ℂ}
    (hz : z ∈ resolventSet ℂ A) (hsigma : sigma ∈ resolventSet ℂ A)
    (hne : z ≠ sigma) :
    (sigma - z)⁻¹ • resolvent A z =
      resolvent A z * resolvent A sigma +
        (sigma - z)⁻¹ • resolvent A sigma := by sorry
