-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.disk_coordinate_errors
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:34:38.254757+00:00
-- url     : https://prove2.me/submissions/7296112a-20e7-4823-9971-55b0c6f657f5

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_abs_eta_le
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_abs_xi_le
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_eta_real_mul
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_eta_sub
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_xi_real_mul
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_xi_sub
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
theorem solution (R : ℝ) (hR : 0 < R) (v w : ℂ)
    (hd : ‖w - (R : ℂ) * v‖ < R / 10) :
    |xi w - R * xi v| < 9 * R / 10 ∧
      |eta w - R * eta v| < 9 * R / 10 ∧
      |xi w| < R * |xi v| + 9 * R / 10 := by
  have hx0 := abs_xi_le (w - (R : ℂ) * v)
  have he0 := abs_eta_le (w - (R : ℂ) * v)
  rw [xi_sub, xi_real_mul] at hx0
  rw [eta_sub, eta_real_mul] at he0
  have hx : |xi w - R * xi v| < 9 * R / 10 := by linarith
  have he : |eta w - R * eta v| < 9 * R / 10 := by linarith
  have hh : |xi w| ≤ |xi w - R * xi v| + |R * xi v| := by
    calc
      |xi w| = |(xi w - R * xi v) + R * xi v| := by congr 1; ring
      _ ≤ |xi w - R * xi v| + |R * xi v| := abs_add_le _ _
  rw [abs_mul, abs_of_pos hR] at hh
  exact ⟨hx, he, by linarith⟩
