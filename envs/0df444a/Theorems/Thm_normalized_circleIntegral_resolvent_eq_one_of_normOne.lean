-- Prove2me | Theorems.Thm_normalized_circleIntegral_resolvent_eq_one_of_normOne
-- name    : normalized_circleIntegral_resolvent_eq_one_of_normOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:19.276262+00:00
-- url     : https://prove2.me/theorems/d5d0acdf-5299-509a-af65-1f330e4461a6
-- title:
--   normalized circle Integral resolvent eq one of norm One: normalized circle Integral resolvent eq one of norm One
-- statement:
--   The normalized resolvent integral on a centered circle enclosing `A` is
--   the identity.  The strict norm bound supplies a uniformly convergent Laurent
--   series on the whole circle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L115-L208
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L115-L208

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

theorem normalized_circleIntegral_resolvent_eq_one_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R = (1 : B) := by sorry
