-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.G1_negative_near
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:29:29.208049+00:00
-- url     : https://prove2.me/submissions/cb3081da-2b8c-4fd5-87d0-ab7b77c81023

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
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



theorem near_coordinates (w : ℂ) (hw : ‖w - centre‖ < 1 / 1000) :
    3 < xi w ∧ xi w < 4 ∧ 3 < eta w ∧ eta w < 5 := by
  have hx := (Complex.abs_re_le_norm (w - centre)).trans_lt hw
  have hy := (Complex.abs_im_le_norm (w - centre)).trans_lt hw
  norm_num [centre, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] at hx hy
  obtain ⟨hx0, hx1⟩ := abs_lt.mp hx
  obtain ⟨hy0, hy1⟩ := abs_lt.mp hy
  unfold xi eta
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (w : ℂ) (hw : ‖w - centre‖ < 1 / 1000) : G1 w < 0 := by
  obtain ⟨hx0, hx1, he0, he1⟩ := near_coordinates w hw
  have hp : l1_23 (xi w) ≤ phi1 (xi w) := by
    unfold phi1
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hl : 9 < l1_23 (xi w) := by unfold l1_23; linarith
  unfold G1
  linarith
