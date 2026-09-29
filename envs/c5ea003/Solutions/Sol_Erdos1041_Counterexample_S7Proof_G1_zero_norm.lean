-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.G1_zero_norm
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:19:06.12599+00:00
-- url     : https://prove2.me/submissions/f57c10b5-a74d-4538-a3ed-71bf88ceab0d

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_graph1_nonpos
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_im_from_coordinates
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_norm_ge_one_of_Hpoly
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_re_from_coordinates
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
theorem solution (w : ℂ) (hw : G1 w = 0) :
    1 ≤ ‖f.eval ((ρ : ℂ) * (ε : ℂ) * w)‖ := by
  have he : eta w = phi1 (xi w) := sub_eq_zero.mp hw
  apply norm_ge_one_of_Hpoly
  have h := graph1_nonpos (xi w)
  unfold Hcoord at h
  rw [← he, ← re_from_coordinates w, ← im_from_coordinates w] at h
  exact h
