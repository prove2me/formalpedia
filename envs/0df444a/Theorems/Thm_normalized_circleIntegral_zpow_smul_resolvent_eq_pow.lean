-- Prove2me | Theorems.Thm_normalized_circleIntegral_zpow_smul_resolvent_eq_pow
-- name    : normalized_circleIntegral_zpow_smul_resolvent_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:52.345617+00:00
-- url     : https://prove2.me/theorems/aef6177e-7a6f-5c01-b215-c0b1211fe400
-- title:
--   normalized circle Integral zpow smul resolvent eq pow: normalized circle Integral zpow smul resolvent eq pow
-- statement:
--   The monomial operator Cauchy formula on any complex Hilbert space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L439-L447
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L439-L447

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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_zpow_smul_resolvent_eq_pow
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by sorry
