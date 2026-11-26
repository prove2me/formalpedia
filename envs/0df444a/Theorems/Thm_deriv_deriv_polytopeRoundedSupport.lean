-- Prove2me | Theorems.Thm_deriv_deriv_polytopeRoundedSupport
-- name    : deriv_deriv_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:26.183451+00:00
-- url     : https://prove2.me/theorems/91f4f929-db49-4466-9da0-9e7d4706a060
-- title:
--   deriv deriv polytope Rounded Support: deriv deriv polytope Rounded Support
-- statement:
--   Adding the rounding constant does not change the second derivative.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L359-L369
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L359-L369

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_deriv_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho theta : ℝ) :
    deriv (deriv (polytopeRoundedSupport u delta rho)) theta =
      polytopeSoftSupportSecond u delta theta := by sorry
