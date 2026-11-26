-- Prove2me | Theorems.Thm_polytopeRoundedSupportCurve_mem_frontier
-- name    : polytopeRoundedSupportCurve_mem_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:10.258017+00:00
-- url     : https://prove2.me/theorems/1aa3e49e-b3b1-55e8-9c96-32f6e9f69c95
-- title:
--   polytope Rounded Support Curve mem frontier: polytope Rounded Support Curve mem frontier
-- statement:
--   Every point of the rounded support curve lies on the frontier of the open
--   rounded support envelope.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L331-L344
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L331-L344

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeRoundedSupportCurve_mem_frontier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      frontier
        (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
