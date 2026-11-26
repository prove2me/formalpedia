-- Prove2me | Theorems.Thm_closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- name    : closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:30.405659+00:00
-- url     : https://prove2.me/theorems/40ce55ec-b1d5-5ce5-97cd-60b614ebb59d
-- title:
--   closure smooth Support Open Envelope polytope Rounded Support: closure smooth Support Open Envelope polytope Rounded Support
-- statement:
--   For positive rounding, the closed support envelope is exactly the closure
--   of its open carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L151-L174
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L151-L174

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem closure_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) =
      smoothSupportClosedEnvelope
        (polytopeRoundedSupport u delta rho) := by sorry
