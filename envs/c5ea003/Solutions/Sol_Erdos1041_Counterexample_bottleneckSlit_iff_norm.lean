-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlit_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:01.502883+00:00
-- url     : https://prove2.me/submissions/162d375d-3145-4f0b-b204-b4323f18ea0b

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
theorem solution (v w : ℂ) (hv : v ≠ 0) :
    w ∈ bottleneckSlit v ↔
      ‖v‖ ≤ ‖w‖ ∧ ‖w‖ < 1 ∧
        w = (‖w‖ : ℂ) * (v / (‖v‖ : ℂ)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by simp [hn]
  rw [bottleneckSlit_iff v w hv]
  constructor
  · rintro ⟨r, hr, hrone, hw⟩
    have hrnonneg : 0 ≤ r := (norm_nonneg v).trans hr
    have hwNorm : ‖w‖ = r := by
      rw [hw]
      simp [abs_of_nonneg hrnonneg, div_self hn]
    exact ⟨hwNorm.symm ▸ hr, hwNorm.symm ▸ hrone, hwNorm.symm ▸ hw⟩
  · rintro ⟨hr, hrone, hw⟩
    exact ⟨‖w‖, hr, hrone, hw⟩
