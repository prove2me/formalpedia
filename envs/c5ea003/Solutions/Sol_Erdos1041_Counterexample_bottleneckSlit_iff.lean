-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneckSlit_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:25:11.133983+00:00
-- url     : https://prove2.me/submissions/a934976d-1121-459a-b49f-e1b4dae1027c

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
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
      ∃ r : ℝ, ‖v‖ ≤ r ∧ r < 1 ∧
        w = (r : ℂ) * (v / (‖v‖ : ℂ)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnC : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hbase : (‖v‖ : ℂ) * (v / (‖v‖ : ℂ)) = v := by
    rw [mul_comm, div_mul_cancel₀ _ hnC]
  constructor
  · rintro ⟨t, ht, ht', hw⟩
    refine ⟨‖v‖ + t, by linarith, by linarith, ?_⟩
    rw [hw, Complex.ofReal_add, add_mul, hbase]
  · rintro ⟨r, hr, hr', hw⟩
    refine ⟨r - ‖v‖, sub_nonneg.mpr hr, by linarith, ?_⟩
    rw [hw, Complex.ofReal_sub, sub_mul, hbase]
    ring
