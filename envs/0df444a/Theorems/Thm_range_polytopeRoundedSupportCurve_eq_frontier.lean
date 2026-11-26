-- Prove2me | Theorems.Thm_range_polytopeRoundedSupportCurve_eq_frontier
-- name    : range_polytopeRoundedSupportCurve_eq_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:05.87273+00:00
-- url     : https://prove2.me/theorems/d90a3b95-d84b-492a-b55a-30e6761bb416
-- title:
--   range polytope Rounded Support Curve eq frontier: range polytope Rounded Support Curve eq frontier
-- statement:
--   The rounded positive-curvature support curve has exactly the frontier of
--   its open support envelope as its range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L195-L206
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L195-L206

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem range_polytopeRoundedSupportCurve_eq_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) =
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
