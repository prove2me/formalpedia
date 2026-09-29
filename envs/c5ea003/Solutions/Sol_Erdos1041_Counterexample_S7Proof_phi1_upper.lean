-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.phi1_upper
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:36.412414+00:00
-- url     : https://prove2.me/submissions/1185be93-2e2a-4872-bafd-17140f708bca

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
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
























theorem affine_le_abs (m b L C x : ℝ)
    (hm0 : -L ≤ m) (hm1 : m ≤ L) (hb : b ≤ C) :
    m * x + b ≤ L * |x| + C := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h := mul_le_mul_of_nonneg_right hm1 hx
    nlinarith
  · rw [abs_of_nonpos hx]
    have h := mul_le_mul_of_nonpos_right hm0 hx
    nlinarith

theorem l1_01_upper (x : ℝ) : l1_01 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_01
  apply affine_le_abs <;> norm_num

theorem l1_12_upper (x : ℝ) : l1_12 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_12
  apply affine_le_abs <;> norm_num

theorem l1_23_upper (x : ℝ) : l1_23 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_23
  apply affine_le_abs <;> norm_num

theorem l1_34_upper (x : ℝ) : l1_34 x ≤ (1 / 4) * |x| + 12 := by
  unfold l1_34
  apply affine_le_abs <;> norm_num
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (x : ℝ) : phi1 x ≤ (1 / 4 : ℝ) * |x| + 12 := by
  unfold phi1
  refine max_le ?_ (max_le (l1_34_upper x)
    (max_le (l1_23_upper x) (max_le (l1_12_upper x) ?_)))
  · simpa using (affine_le_abs (-(3 / 14)) 0 (1 / 4) 12 x
      (by norm_num) (by norm_num) (by norm_num))
  · exact (min_le_left _ _).trans (l1_01_upper x)
