-- Prove2me | Theorems.Thm_exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
-- name    : exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:21.801311+00:00
-- url     : https://prove2.me/theorems/74de5564-7fbb-4509-a1ee-4c93d80e9638
-- title:
--   exists polynomial tendsto Uniformly On interval Integral mul inv sub of is Compact convex: exists polynomial tendsto Uniformly On interval Integral mul inv sub of is Compact convex
-- statement:
--   A continuous interval integral of Cauchy kernels whose poles stay outside
--   a compact convex planar set is a compact-uniform limit of polynomials.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeIntegral.lean#L195-L221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeIntegral.lean#L195-L221

import Definitions.Def_Operator_Crouzeix_ConvexRungeClosure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Topology Interval

theorem exists_polynomial_tendstoUniformlyOn_intervalIntegral_mul_inv_sub_of_isCompact_convex
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (coeff pole : ℝ → ℂ) (hcoeff : Continuous coeff)
    (hpole_cont : Continuous pole) (hpole : ∀ t, pole t ∉ K)
    {a b : ℝ} (hab : a < b) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn
        (fun n z => Polynomial.eval z (q n))
        (fun z => ∫ t in a..b, coeff t * (pole t - z)⁻¹)
        atTop K := by sorry
