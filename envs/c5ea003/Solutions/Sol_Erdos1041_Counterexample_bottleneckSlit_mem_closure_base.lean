-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlit_mem_closure_base
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:02.892073+00:00
-- url     : https://prove2.me/submissions/074a3174-3a5f-4dad-9a13-9f22f896a4e2

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlit_iff
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
open Topology

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (v : ℂ) (hv : v ≠ 0) (ξ : ℂ)
    (hξ : ξ ∈ bottleneckSlit v) : ξ ∈ closure (bottleneckSlitBase v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by simp [hn]
  obtain ⟨r, hr, hrone, hxi⟩ := (bottleneckSlit_iff v ξ hv).mp hξ
  have hrnonneg : 0 ≤ r := (norm_nonneg v).trans hr
  have hu0 : v / (‖v‖ : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  rw [Metric.mem_closure_iff]
  intro ε hε
  set τ : ℝ := min (ε / 2) ((1 - r) / 2) with hτdef
  have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
  have hτε : τ ≤ ε / 2 := min_le_left _ _
  have hτr : τ ≤ (1 - r) / 2 := min_le_right _ _
  refine ⟨(((r : ℂ) + (τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ))), ⟨?_, ?_⟩, ?_⟩
  · -- inside the unit disc
    have hbound : ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ ≤ r + τ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnonneg, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hτpos.le]
    rw [norm_mul, hunit, mul_one]
    linarith
  · -- off the slit
    intro hmem
    obtain ⟨ρ, -, -, hρ⟩ := (bottleneckSlit_iff v _ hv).mp hmem
    have hcancel : (r : ℂ) + (τ : ℂ) * Complex.I = (ρ : ℂ) :=
      mul_right_cancel₀ hu0 hρ
    have him := congrArg Complex.im hcancel
    simp at him
    exact absurd him hτpos.ne'
  · -- close to `ξ`
    have hdiff : ξ - ((r : ℂ) + (τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ)) =
        (-(τ : ℂ) * Complex.I) * (v / (‖v‖ : ℂ)) := by
      rw [hxi]; ring
    rw [dist_eq_norm, hdiff, norm_mul, hunit, mul_one, norm_mul, Complex.norm_I,
      mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτpos.le]
    linarith
