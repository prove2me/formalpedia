-- Prove2me | Theorems.Thm_polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
-- name    : polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:15.455473+00:00
-- url     : https://prove2.me/theorems/84a84cfa-79bf-441e-b62d-faef763a4305
-- title:
--   polytope Rounded Support Curve mem smooth Support Closed Envelope: polytope Rounded Support Curve mem smooth Support Closed Envelope
-- statement:
--   Every point of the rounded support curve belongs to its closed support
--   envelope.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L314-L327
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L314-L327

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeRoundedSupportCurve_mem_smoothSupportClosedEnvelope
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    polytopeRoundedSupportCurve u delta rho theta ∈
      smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) := by sorry
