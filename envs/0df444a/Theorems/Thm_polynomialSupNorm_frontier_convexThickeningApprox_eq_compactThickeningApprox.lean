-- Prove2me | Theorems.Thm_polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
-- name    : polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:07.688864+00:00
-- url     : https://prove2.me/theorems/c50d8229-108a-41ef-945b-c9b8f22eadb3
-- title:
--   polynomial Sup Norm frontier convex Thickening Approx eq compact Thickening Approx: polynomial Sup Norm frontier convex Thickening Approx eq compact Thickening Approx
-- statement:
--   For a bounded set, the polynomial sup-norm on the frontier of its open
--   thickening equals the norm on the closed thickening at the same radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryApproximation.lean#L35-L43
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/BoundaryApproximation.lean#L35-L43

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
set_option autoImplicit false
open Filter Polynomial Set

theorem polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
    (p : Polynomial ℂ) {K : Set ℂ} (hK : Bornology.IsBounded K) (n : ℕ) :
    polynomialSupNorm p (frontier (convexThickeningApprox K n)) =
      polynomialSupNorm p (compactThickeningApprox K n) := by sorry
