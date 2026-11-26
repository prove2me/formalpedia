-- Prove2me | Theorems.Thm_exists_sub_int_mul_two_pi_mem_Ico
-- name    : exists_sub_int_mul_two_pi_mem_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:20.102945+00:00
-- url     : https://prove2.me/theorems/dbdeabd4-cf2a-422e-ada2-15c85ee60aff
-- title:
--   exists sub int mul two pi mem Ico: exists sub int mul two pi mem Ico
-- statement:
--   Every real angle has an integer-period translate in the half-open interval
--   centered at any prescribed angle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L135-L149
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L135-L149

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem exists_sub_int_mul_two_pi_mem_Ico (theta phi : ℝ) :
    ∃ k : ℤ,
      phi - (k : ℝ) * (2 * Real.pi) ∈
        Ico (theta - Real.pi) (theta + Real.pi) := by sorry
