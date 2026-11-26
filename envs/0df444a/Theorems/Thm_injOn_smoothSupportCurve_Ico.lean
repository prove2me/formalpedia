-- Prove2me | Theorems.Thm_injOn_smoothSupportCurve_Ico
-- name    : injOn_smoothSupportCurve_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:36.773087+00:00
-- url     : https://prove2.me/theorems/f66b5602-1883-5193-bb04-91559a258972
-- title:
--   inj On smooth Support Curve Ico: inj On smooth Support Curve Ico
-- statement:
--   A smooth periodic positive-curvature support curve is injective on every
--   half-open fundamental period.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L242-L267
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L242-L267

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem injOn_smoothSupportCurve_Ico
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (a : ℝ) :
    Set.InjOn (smoothSupportCurve h) (Ico a (a + 2 * Real.pi)) := by sorry
