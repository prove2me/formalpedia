-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.cert_tail_B
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:57.825103+00:00
-- url     : https://prove2.me/submissions/0310a31c-360c-4996-b306-5ce7f7d95712

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
    Hpoly (32 + (34 - 32) * r) ((-16) + ((-17) - (-16)) * r) ≤ 0 := by
  have hid : Hpoly (32 + (34 - 32) * r) ((-16) + ((-17) - (-16)) * r) = -((
      74626014491510871756241612863999999970345081825237401599998588293683936671825919999999999999999999999999999999999999
      + 32648688932044992799062153215999999990732838070386687999999470610131476251934720000000000000000000000000000000000000 * r
      + 6121603699285524814287076863999999998841604758798335999999917282833043164364800000000000000000000000000000000000000 * r ^ 2
      + 637665691883761092261961535999999999927600297424895999999993106902753597030400000000000000000000000000000000000000 * r ^ 3
      + 39854080000000001441593148999999999997737509294527999999999676886066574860800000000000000000000000000000000000000 * r ^ 4
      + 1494527999999999999999999999999999999971718866181599999999991922151664371520000000000000000000000000000000000000 * r ^ 5
      + 31135999999999999999999999999999999999999999999999999999999915855746503870000000000000000000000000000000000000 * r ^ 6
      + 278000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * r ^ 7) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
    unfold Hpoly
    ring
  rw [hid]
  exact neg_nonpos.mpr (by positivity)
