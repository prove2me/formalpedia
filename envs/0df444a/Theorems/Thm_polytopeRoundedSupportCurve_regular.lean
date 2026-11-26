-- Prove2me | Theorems.Thm_polytopeRoundedSupportCurve_regular
-- name    : polytopeRoundedSupportCurve_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:28.703734+00:00
-- url     : https://prove2.me/theorems/802f4d83-7242-5414-b002-658cebfbd1e2
-- title:
--   polytope Rounded Support Curve regular: polytope Rounded Support Curve regular
-- statement:
--   Positive smoothing and rounding scales make the rounded polytope support
--   curve regular.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L222-L231
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L222-L231

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeRoundedSupportCurve_regular
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by sorry
