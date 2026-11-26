-- Prove2me | Theorems.Thm_hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
-- name    : hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:40.175241+00:00
-- url     : https://prove2.me/theorems/7769c6ad-2252-5834-8dc1-a87e5347b91f
-- title:
--   has Smooth Jordan Outer Approximation For Polytopes of support Curve range: has Smooth Jordan Outer Approximation For Polytopes of support Curve range
-- statement:
--   The full-dimensional finite-polytope approximation problem follows from
--   frontier surjectivity of every positive rounded support curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L75-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L75-L93

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace

theorem hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
    (hrange : ∀ {u : Finset ℂ} (_hu : u.Nonempty) {delta rho : ℝ},
      0 < delta → 0 < rho →
      Set.range (polytopeRoundedSupportCurve u delta rho) =
        frontier (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho))) :
    HasSmoothJordanOuterApproximationForPolytopes := by sorry
