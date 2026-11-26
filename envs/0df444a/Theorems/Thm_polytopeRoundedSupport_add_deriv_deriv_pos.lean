-- Prove2me | Theorems.Thm_polytopeRoundedSupport_add_deriv_deriv_pos
-- name    : polytopeRoundedSupport_add_deriv_deriv_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:21.400914+00:00
-- url     : https://prove2.me/theorems/8fe13a7d-ad4b-5244-a0a4-0e8e8cfe36af
-- title:
--   polytope Rounded Support add deriv deriv pos: polytope Rounded Support add deriv deriv pos
-- statement:
--   A positive rounding constant gives strictly positive support-curve
--   curvature radius everywhere.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L373-L380
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L373-L380

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeRoundedSupport_add_deriv_deriv_pos
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < polytopeRoundedSupport u delta rho theta +
      deriv (deriv (polytopeRoundedSupport u delta rho)) theta := by sorry
