-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.segment_g1_01
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:58.443401+00:00
-- url     : https://prove2.me/submissions/a2c7a358-2671-4200-bd7a-56cb4976f4f8

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

theorem cert_g1_01_0 (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Hpoly ((-25) + ((-11 / 2) - (-25)) * r) ((125 / 4) + ((61 / 10) - (125 / 4)) * r) ≤ 0 := by
  have ht : 0 ≤ 1 - r := by linarith
  have hid : Hpoly ((-25) + ((-11 / 2) - (-25)) * r) ((125 / 4) + ((61 / 10) - (125 / 4)) * r) = -((
      164401906390677567802891262023925781181092407447879791259767445585952452382445335388183593749999999999999999999999999 * (1 - r) ^ 7
      + 235659396324495879252499551110839843542581765487857818603519514683105976106829643249511718749999999999999999999999993 * r * (1 - r) ^ 6
      + 144304839920034110278122964243652343513870579984451976318362413376586710561939239501953124999999999999999999999999979 * r ^ 2 * (1 - r) ^ 5
      + 48948843777284975929556156609575781118749428673152907958985583326316537387223779296874999999999999999999999999999965 * r ^ 3 * (1 - r) ^ 4
      + 9938728816462879549808867669042999960191564121065792093125271682698272736348218749999999999999999999999999999999965 * r ^ 4 * (1 - r) ^ 3
      + 1208481847794385574980041626041499993240494990324034389550034964210218546065368688749999999999999999999999999999979 * r ^ 5 * (1 - r) ^ 2
      + 81481153208220097901757962553999999394853179790815546600002395763318043997296953399999999999999999999999999999993 * r ^ 6 * (1 - r)
      + 2348449496126948251602552717999999977715581853614265800000067368021684611299358399999999999999999999999999999999 * r ^ 7) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
    unfold Hpoly
    ring
  rw [hid]
  exact neg_nonpos.mpr (by positivity)
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Hpoly ((-25) + ((-11 / 2) - (-25)) * r) ((125 / 4) + ((61 / 10) - (125 / 4)) * r) ≤ 0 := by
  exact cert_g1_01_0 r hr0 hr1
