-- Prove2me | Theorems.Thm_exists_tight_polytopeRoundedSupportEnvelope
-- name    : exists_tight_polytopeRoundedSupportEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:01.252965+00:00
-- url     : https://prove2.me/theorems/ee011f7b-1ee9-5607-a28e-a7d59c4e9296
-- title:
--   exists tight polytope Rounded Support Envelope: exists tight polytope Rounded Support Envelope
-- statement:
--   Every nonempty finite convex hull has positive log-sum-exp smoothing
--   and rounding scales whose open envelope contains the hull while the closure
--   of that envelope stays in a prescribed metric thickening.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeTight.lean#L18-L69
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeTight.lean#L18-L69

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem exists_tight_polytopeRoundedSupportEnvelope
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) := by sorry
