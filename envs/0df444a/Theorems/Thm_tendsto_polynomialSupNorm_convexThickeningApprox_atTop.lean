-- Prove2me | Theorems.Thm_tendsto_polynomialSupNorm_convexThickeningApprox_atTop
-- name    : tendsto_polynomialSupNorm_convexThickeningApprox_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:29:57.771425+00:00
-- url     : https://prove2.me/theorems/d5cba25b-7aea-53cd-9f74-a9ea983014b4
-- title:
--   tendsto polynomial Sup Norm convex Thickening Approx at Top: tendsto polynomial Sup Norm convex Thickening Approx at Top
-- statement:
--   Polynomial sup-norms on the explicit open metric thickenings of a compact
--   set converge to the sup-norm on that set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L190-L211
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ApproximationSupNorm.lean#L190-L211

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
set_option autoImplicit false
open Filter Polynomial Set

theorem tendsto_polynomialSupNorm_convexThickeningApprox_atTop
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n ↦ polynomialSupNorm p (convexThickeningApprox K n)) atTop
      (nhds (polynomialSupNorm p K)) := by sorry
