-- Prove2me | Theorems.Thm_contDiff_polytopeRoundedSupport
-- name    : contDiff_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:26.413155+00:00
-- url     : https://prove2.me/theorems/531a87f3-06c7-4e3e-8d34-b73b6289d8a4
-- title:
--   cont Diff polytope Rounded Support: cont Diff polytope Rounded Support
-- statement:
--   The rounded support remains infinitely differentiable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L352-L356
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L352-L356

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupport u delta rho) := by sorry
