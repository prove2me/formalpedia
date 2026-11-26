-- Prove2me | Theorems.Thm_periodic_deriv_of_periodic
-- name    : periodic_deriv_of_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:41.297563+00:00
-- url     : https://prove2.me/theorems/6c10fe24-00a7-417d-bd3a-f96ac1851719
-- title:
--   periodic deriv of periodic: periodic deriv of periodic
-- statement:
--   Differentiation preserves an additive period.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L41-L48
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L41-L48

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_deriv_of_periodic {f : ℝ → ℝ} {p : ℝ}
    (hf : Function.Periodic f p) :
    Function.Periodic (deriv f) p := by sorry
