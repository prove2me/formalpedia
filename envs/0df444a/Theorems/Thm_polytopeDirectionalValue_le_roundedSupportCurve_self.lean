-- Prove2me | Theorems.Thm_polytopeDirectionalValue_le_roundedSupportCurve_self
-- name    : polytopeDirectionalValue_le_roundedSupportCurve_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:25.218228+00:00
-- url     : https://prove2.me/theorems/07680949-a895-46ba-bcbf-c3d24846e2db
-- title:
--   polytope Directional Value le rounded Support Curve self: polytope Directional Value le rounded Support Curve self
-- statement:
--   In every direction, the rounded support curve lies on a supporting line
--   outside the entire original finite convex hull.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L235-L246
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L235-L246

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeDirectionalValue_le_roundedSupportCurve_self
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 ≤ rho)
    (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeDirectionalValue
        (polytopeRoundedSupportCurve u delta rho theta) theta := by sorry
