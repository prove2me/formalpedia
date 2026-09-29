-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.phi1_region_2
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T23:21:26.805558+00:00
-- url     : https://prove2.me/submissions/3596e74d-a7b8-4b60-bdf0-281a3710665c

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
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (x : ℝ) (hlo : (3615717603167 / 500000000000) ≤ x) (hhi : x ≤ (519 / 10)) :
    phi1 x = l1_12 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith
