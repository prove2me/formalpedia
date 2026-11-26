-- Prove2me | Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne
-- name    : normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:53:33.835443+00:00
-- url     : https://prove2.me/theorems/4056c725-4c51-464b-8fa0-045fa1181253
-- title:
--   normalized circle Integral eval smul resolvent eq aeval of norm One: normalized circle Integral eval smul resolvent eq aeval of norm One
-- statement:
--   The operator-valued Cauchy formula for polynomials on a centered circle:
--   integrating `p(z) R_A(z)` recovers `p(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L280-L305
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleCauchy.lean#L280-L305

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

theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
        Polynomial.aeval A p := by sorry
