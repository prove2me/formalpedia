-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.phi1_region_4
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T23:31:03.295948+00:00
-- url     : https://prove2.me/submissions/3efb4c94-a821-4cab-9ce0-858ae65bd3ff

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
theorem solution (x : ℝ) (hlo : (-224) ≤ x) (hhi : x ≤ (-717965515391 / 40000000000)) :
    phi1 x = l1_34 x := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  simp only [max_def, min_def]
  split_ifs <;> linarith
