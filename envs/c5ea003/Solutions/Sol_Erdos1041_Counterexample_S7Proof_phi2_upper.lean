-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.phi2_upper
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:39:07.517636+00:00
-- url     : https://prove2.me/submissions/8c7e202c-d623-4c69-930c-04071ccdc02b

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









theorem l2_01_upper (x : ℝ) : l2_01 x ≤ 1 * |x| + 18 := by
  unfold l2_01
  apply affine_le_abs <;> norm_num

theorem l2_12_upper (x : ℝ) : l2_12 x ≤ 1 * |x| + 18 := by
  unfold l2_12
  apply affine_le_abs <;> norm_num

theorem l2_23_upper (x : ℝ) : l2_23 x ≤ 1 * |x| + 18 := by
  unfold l2_23
  apply affine_le_abs <;> norm_num
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (x : ℝ) : phi2 x ≤ |x| + 18 := by
  unfold phi2
  refine max_le ?_ (max_le (by simpa using l2_23_upper x)
    (max_le (by simpa using l2_12_upper x) (max_le (by simpa using l2_01_upper x) ?_)))
  · simpa using (affine_le_abs (-(37 / 46)) 0 1 18 x
      (by norm_num) (by norm_num) (by norm_num))
  · simpa using (affine_le_abs (4 / 5) 0 1 18 x
      (by norm_num) (by norm_num) (by norm_num))
