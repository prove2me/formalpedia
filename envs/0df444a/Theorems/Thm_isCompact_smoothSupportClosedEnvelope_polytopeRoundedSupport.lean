-- Prove2me | Theorems.Thm_isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
-- name    : isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:48.221772+00:00
-- url     : https://prove2.me/theorems/a4f80617-f063-4f13-9f72-d249f68344b1
-- title:
--   is Compact smooth Support Closed Envelope polytope Rounded Support: is Compact smooth Support Closed Envelope polytope Rounded Support
-- statement:
--   The rounded support envelope of a nonempty finite point set is compact.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L113-L126
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L113-L126

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem isCompact_smoothSupportClosedEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    IsCompact
      (smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
