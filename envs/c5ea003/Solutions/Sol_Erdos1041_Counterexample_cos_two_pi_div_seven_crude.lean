-- Prove2me | solution 1 for Erdos1041.Counterexample.cos_two_pi_div_seven_crude
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:26:19.015881+00:00
-- url     : https://prove2.me/submissions/25cea7e2-a556-412d-9ee5-c117d404afa1

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open scoped ComplexConjugate NNReal

namespace Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
theorem two_pi_div_seven_lb : (8975977 / 10 ^ 7 : ℝ) < 2 * Real.pi / 7 := by
  have h := Real.pi_gt_d6
  norm_num at h ⊢
  linarith
theorem two_pi_div_seven_ub : 2 * Real.pi / 7 < (8975980 / 10 ^ 7 : ℝ) := by
  have h := Real.pi_lt_d6
  norm_num at h ⊢
  linarith
theorem two_pi_div_seven_pos : 0 < 2 * Real.pi / 7 := by
  have := two_pi_div_seven_lb; linarith
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    (5630 / 10000 : ℝ) < Real.cos (2 * Real.pi / 7) ∧
      Real.cos (2 * Real.pi / 7) < (6312 / 10000 : ℝ) := by
  have hlb := two_pi_div_seven_lb
  have hub := two_pi_div_seven_ub
  have hpos := two_pi_div_seven_pos
  have habs : |2 * Real.pi / 7| ≤ 1 := by
    rw [abs_of_pos hpos]; linarith
  have hb := Real.cos_bound habs
  rw [abs_of_pos hpos] at hb
  rw [abs_le] at hb
  have h2u : (2 * Real.pi / 7) ^ 2 < 8056822 / 10 ^ 7 := by nlinarith
  have h2l : (8056816 / 10 ^ 7 : ℝ) < (2 * Real.pi / 7) ^ 2 := by nlinarith
  have h4u : (2 * Real.pi / 7) ^ 4 < 6492000 / 10 ^ 7 := by nlinarith
  constructor
  · nlinarith [hb.1]
  · nlinarith [hb.2]
