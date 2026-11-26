-- Prove2me | Theorems.Thm_convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- name    : convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:57.040908+00:00
-- url     : https://prove2.me/theorems/733cca0d-ff6d-4ff0-b8f0-878eb97110dc
-- title:
--   convex Hull subset smooth Support Open Envelope polytope Rounded Support: convex Hull subset smooth Support Open Envelope polytope Rounded Support
-- statement:
--   The convex hull lies in the open rounded-support envelope, with `rho` as
--   an explicit uniform interior margin.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L121-L141
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L121-L141

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
    {u : Finset ℂ} {delta rho : ℝ} (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    convexHull ℝ (u : Set ℂ) ⊆
      smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho) := by sorry
