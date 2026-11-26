-- Prove2me | Theorems.Thm_nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- name    : nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:50.022281+00:00
-- url     : https://prove2.me/theorems/a52225b2-d546-451d-929b-56015b0f102c
-- title:
--   nonempty smooth Support Open Envelope polytope Rounded Support: nonempty smooth Support Open Envelope polytope Rounded Support
-- statement:
--   Positive rounding makes the open support envelope nonempty.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L139-L147
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L139-L147

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem nonempty_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (smoothSupportOpenEnvelope
      (polytopeRoundedSupport u delta rho)).Nonempty := by sorry
