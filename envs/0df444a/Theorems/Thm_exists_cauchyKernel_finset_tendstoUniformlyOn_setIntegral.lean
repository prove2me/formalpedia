-- Prove2me | Theorems.Thm_exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
-- name    : exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:43.37863+00:00
-- url     : https://prove2.me/theorems/b77dbf5a-f384-4483-aae2-02fdbd32bf3f
-- title:
--   exists cauchy Kernel finset tendsto Uniformly On set Integral: exists cauchy Kernel finset tendsto Uniformly On set Integral
-- statement:
--   A continuous exterior-kernel integral is the compact-uniform limit of
--   finite kernel sums sampled from its parameter interval.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeIntegral.lean#L82-L153
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ConvexRungeIntegral.lean#L82-L153

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

theorem exists_cauchyKernel_finset_tendstoUniformlyOn_setIntegral
    (K : Set ℂ) (hK : IsCompact K)
    (coeff : ℝ → ℂ) (pole : ℝ → ℂ)
    (hcoeff : Continuous coeff) (hpole_cont : Continuous pole)
    (hpole : ∀ t, pole t ∉ K) {a b : ℝ} (hab : a < b) :
    ∃ (s : ℕ → Finset (Ioc a b)) (w : ℕ → Ioc a b → ℝ),
      TendstoUniformlyOn
        (fun n z ↦ ∑ t ∈ s n,
          ((w n t : ℝ) : ℂ) * coeff t * (pole t - z)⁻¹)
        (fun z ↦ ∫ t in Ioc a b, coeff t * (pole t - z)⁻¹)
        atTop K := by sorry
