-- Prove2me | Theorems.Thm_tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop
-- name    : tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:10.135106+00:00
-- url     : https://prove2.me/theorems/51ad01cd-8bb4-4d61-a28f-181a0f124a46
-- title:
--   tendsto polynomial Sup Norm frontier convex Thickening Approx at Top: tendsto polynomial Sup Norm frontier convex Thickening Approx at Top
-- statement:
--   For a compact target, polynomial sup-norms on the frontiers of the
--   explicit open thickenings converge to the target sup-norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryApproximation.lean#L47-L65
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryApproximation.lean#L47-L65

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
set_option autoImplicit false
open Filter Polynomial Set

theorem tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto
      (fun n ↦ polynomialSupNorm p (frontier (convexThickeningApprox K n))) atTop
      (nhds (polynomialSupNorm p K)) := by sorry
