-- Prove2me | solution 1 for Erdos1041.Counterexample.cos_two_pi_div_seven_bounds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:29:06.186978+00:00
-- url     : https://prove2.me/submissions/49bfb078-6f7f-4f8b-ae09-975135893f4b

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Theorems.Thm_Erdos1041_Counterexample_cos_two_pi_div_seven_crude
import Theorems.Thm_Erdos1041_Counterexample_cos_two_pi_div_seven_cubic
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
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    (6234 / 10000 : ℝ) < Real.cos (2 * Real.pi / 7) ∧
      Real.cos (2 * Real.pi / 7) < (6236 / 10000 : ℝ) := by
  obtain ⟨h1, h2⟩ := cos_two_pi_div_seven_crude
  have hg := cos_two_pi_div_seven_cubic
  have hq : ∀ a : ℝ, 56 / 100 ≤ a → a ≤ 64 / 100 →
      0 < 8 * (Real.cos (2 * Real.pi / 7) ^ 2 + Real.cos (2 * Real.pi / 7) * a + a ^ 2)
        + 4 * (Real.cos (2 * Real.pi / 7) + a) - 4 := by
    intro a ha1 ha2
    nlinarith [h1, h2, ha1, ha2,
      mul_pos (show (0:ℝ) < Real.cos (2 * Real.pi / 7) by linarith)
        (show (0:ℝ) < a by linarith)]
  constructor
  · by_contra hcon
    push_neg at hcon
    have hq' := hq (6234 / 10000) (by norm_num) (by norm_num)
    have hid : (0 : ℝ) - (8 * (6234 / 10000 : ℝ) ^ 3 + 4 * (6234 / 10000 : ℝ) ^ 2
          - 4 * (6234 / 10000 : ℝ) - 1)
        = (Real.cos (2 * Real.pi / 7) - 6234 / 10000) *
          (8 * (Real.cos (2 * Real.pi / 7) ^ 2
              + Real.cos (2 * Real.pi / 7) * (6234 / 10000) + (6234 / 10000 : ℝ) ^ 2)
            + 4 * (Real.cos (2 * Real.pi / 7) + 6234 / 10000) - 4) := by
      linear_combination (-1 : ℝ) * hg
    nlinarith [hid, hq', hcon]
  · by_contra hcon
    push_neg at hcon
    have hq' := hq (6236 / 10000) (by norm_num) (by norm_num)
    have hid : (0 : ℝ) - (8 * (6236 / 10000 : ℝ) ^ 3 + 4 * (6236 / 10000 : ℝ) ^ 2
          - 4 * (6236 / 10000 : ℝ) - 1)
        = (Real.cos (2 * Real.pi / 7) - 6236 / 10000) *
          (8 * (Real.cos (2 * Real.pi / 7) ^ 2
              + Real.cos (2 * Real.pi / 7) * (6236 / 10000) + (6236 / 10000 : ℝ) ^ 2)
            + 4 * (Real.cos (2 * Real.pi / 7) + 6236 / 10000) - 4) := by
      linear_combination (-1 : ℝ) * hg
    nlinarith [hid, hq', hcon]
