-- Prove2me | Theorems.Thm_normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
-- name    : normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:33.954437+00:00
-- url     : https://prove2.me/theorems/22a24d30-d91e-5406-8702-dec084270e9d
-- title:
--   normalized circle Integral zpow smul resolvent eq pow of norm One: normalized circle Integral zpow smul resolvent eq pow of norm One
-- statement:
--   The normalized resolvent integral sends the scalar monomial `z^n` to
--   the algebra power `A^n`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L228-L268
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L228-L268

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]

theorem normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by sorry
