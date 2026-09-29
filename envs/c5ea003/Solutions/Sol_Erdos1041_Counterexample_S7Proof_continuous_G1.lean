-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.continuous_G1
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:25:09.355003+00:00
-- url     : https://prove2.me/submissions/39220ca7-abb7-4313-8b40-0f78615f7a16

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













theorem continuous_phi1 : Continuous phi1 := by
  unfold phi1 l1_01 l1_12 l1_23 l1_34
  fun_prop
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution : Continuous G1 :=
  continuous_eta.sub (continuous_phi1.comp continuous_xi)
