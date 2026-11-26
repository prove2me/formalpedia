-- Prove2me | Theorems.Thm_closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
-- name    : closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:56.095924+00:00
-- url     : https://prove2.me/theorems/14cf6e94-205e-41b3-a421-e8dd9dbf8024
-- title:
--   closure smooth Support Open Envelope polytope Rounded Support subset cthickening: closure smooth Support Open Envelope polytope Rounded Support subset cthickening
-- statement:
--   The closure of the open rounded-support carrier obeys the same explicit
--   outer thickening bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L178-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeApproximation.lean#L178-L191

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    closure
        (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho)) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by sorry
