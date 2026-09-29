-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.continuous_G2
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:25:09.967053+00:00
-- url     : https://prove2.me/submissions/1bd5b7a3-4f82-451b-8420-b3ddbfc67399

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_continuous_eta
import Theorems.Thm_Erdos1041_Counterexample_S7Proof_continuous_xi
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















theorem continuous_phi2 : Continuous phi2 := by
  unfold phi2 l2_01 l2_12 l2_23
  fun_prop
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution : Continuous G2 :=
  continuous_eta.neg.sub (continuous_phi2.comp continuous_xi)
