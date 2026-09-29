-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.G1_positive_disk
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:36:58.496766+00:00
-- url     : https://prove2.me/submissions/3f8b5c04-5194-4367-b51d-5c9917a54c1a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_disk_coordinate_errors
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_upper
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

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

noncomputable section

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (R : ℝ) (hR : 100 ≤ R) (v w : ℂ)
    (hc : 3 / 2 ≤ eta v - (1 / 4 : ℝ) * |xi v|)
    (hd : ‖w - (R : ℂ) * v‖ < R / 10) : 0 < G1 w := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hx, he, ha⟩ := disk_coordinate_errors R hR0 v w hd
  obtain ⟨he0, he1⟩ := abs_lt.mp he
  have hp := phi1_upper (xi w)
  have hcR := mul_le_mul_of_nonneg_left hc hR0.le
  unfold G1
  nlinarith
