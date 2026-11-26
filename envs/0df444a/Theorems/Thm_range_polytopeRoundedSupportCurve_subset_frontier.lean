-- Prove2me | Theorems.Thm_range_polytopeRoundedSupportCurve_subset_frontier
-- name    : range_polytopeRoundedSupportCurve_subset_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:08.130603+00:00
-- url     : https://prove2.me/theorems/f3a62fb5-103d-538c-bd96-a43825514215
-- title:
--   range polytope Rounded Support Curve subset frontier: range polytope Rounded Support Curve subset frontier
-- statement:
--   The range of the rounded support curve is contained in the frontier of
--   its open support envelope.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L348-L355
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L348-L355

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem range_polytopeRoundedSupportCurve_subset_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    range (polytopeRoundedSupportCurve u delta rho) ⊆
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
