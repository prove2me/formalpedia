-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.cert_tail_C
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:40:55.398806+00:00
-- url     : https://prove2.me/submissions/058a1c74-87d3-4dc0-8154-9caf931a2a58

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
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
theorem solution (r : ℝ) (hr0 : 0 ≤ r) :
    Hpoly ((-44) + ((-45) - (-44)) * r) (0 + (0 - 0) * r) ≤ 0 := by
  have hid : Hpoly ((-44) + ((-45) - (-44)) * r) (0 + (0 - 0) * r) = -((
      319260298355308618310075079999999999999999999703150796800005218607817227903999999999999999999999999999999999999999999
      + 50793001600771427678189279999999999999999999966267136000000711628338712896000000000000000000000000000000000000000000 * r
      + 3463213519672495807779179999999999999999999998466688000000040433428335960000000000000000000000000000000000000000000 * r ^ 2
      + 131183154058124963754229999999999999999999999965152000000001225255404120000000000000000000000000000000000000000000 * r ^ 3
      + 2981439999999999794058124999999999999999999999604000000000020885035297500000000000000000000000000000000000000000 * r ^ 4
      + 40655999999999999999999999999999999999999999998200000000000189863957250000000000000000000000000000000000000000 * r ^ 5
      + 308000000000000000000000000000000000000000000000000000000000719181656250000000000000000000000000000000000000 * r ^ 6
      + 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * r ^ 7) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
    unfold Hpoly
    ring
  rw [hid]
  exact neg_nonpos.mpr (by positivity)
