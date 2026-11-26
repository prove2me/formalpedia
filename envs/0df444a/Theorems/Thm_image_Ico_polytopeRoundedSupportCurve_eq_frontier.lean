-- Prove2me | Theorems.Thm_image_Ico_polytopeRoundedSupportCurve_eq_frontier
-- name    : image_Ico_polytopeRoundedSupportCurve_eq_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:49.718914+00:00
-- url     : https://prove2.me/theorems/cbceec15-a046-53fa-a687-0b54997eefbf
-- title:
--   image Ico polytope Rounded Support Curve eq frontier: image Ico polytope Rounded Support Curve eq frontier
-- statement:
--   The rounded support curve parametrizes its whole frontier already on the
--   standard half-open interval `[0, 2 * pi)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L221-L236
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L221-L236

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem image_Ico_polytopeRoundedSupportCurve_eq_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    polytopeRoundedSupportCurve u delta rho '' Ico 0 (2 * Real.pi) =
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
