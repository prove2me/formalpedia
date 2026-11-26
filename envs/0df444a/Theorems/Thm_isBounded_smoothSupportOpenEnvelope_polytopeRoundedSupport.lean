-- Prove2me | Theorems.Thm_isBounded_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- name    : isBounded_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:00.832293+00:00
-- url     : https://prove2.me/theorems/2d440f8b-bee9-5c6f-8f9c-ac1b93b311be
-- title:
--   is Bounded smooth Support Open Envelope polytope Rounded Support: is Bounded smooth Support Open Envelope polytope Rounded Support
-- statement:
--   The open rounded-support carrier is bounded.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L129-L136
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L129-L136

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem isBounded_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    Bornology.IsBounded
      (smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho)) := by sorry
