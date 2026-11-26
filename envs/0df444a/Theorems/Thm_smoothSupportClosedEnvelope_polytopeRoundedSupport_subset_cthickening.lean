-- Prove2me | Theorems.Thm_smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
-- name    : smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:46.473191+00:00
-- url     : https://prove2.me/theorems/fac8af7c-5246-4822-ad37-16faf902395b
-- title:
--   smooth Support Closed Envelope polytope Rounded Support subset cthickening: smooth Support Closed Envelope polytope Rounded Support subset cthickening
-- statement:
--   The rounded support envelope lies in the closed thickening of the finite
--   convex hull by the exact uniform support overshoot.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L52-L110
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L52-L110

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by sorry
