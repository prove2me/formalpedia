-- Prove2me | Theorems.Thm_exists_polynomialSupNorm_convexThickeningApprox_le_add
-- name    : exists_polynomialSupNorm_convexThickeningApprox_le_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:22.096386+00:00
-- url     : https://prove2.me/theorems/fb3dabf9-c527-458c-a5af-d37e3f9d57dd
-- title:
--   exists polynomial Sup Norm convex Thickening Approx le add: exists polynomial Sup Norm convex Thickening Approx le add
-- statement:
--   Every positive error tolerance is achieved by one of the explicit open
--   metric thickenings of a compact set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L165-L186
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L165-L186

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Filter Polynomial Set

theorem exists_polynomialSupNorm_convexThickeningApprox_le_add
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      polynomialSupNorm p (convexThickeningApprox K n) ≤
        polynomialSupNorm p K + ε := by sorry
