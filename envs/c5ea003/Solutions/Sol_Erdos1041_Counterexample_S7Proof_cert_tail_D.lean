-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.cert_tail_D
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:41:45.344986+00:00
-- url     : https://prove2.me/submissions/634c8cc1-2fbc-4d26-a750-a348f94beb9d

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
    Hpoly (10 + (12 - 10) * r) ((-45) + ((-54) - (-45)) * r) ≤ 0 := by
  have hid : Hpoly (10 + (12 - 10) * r) ((-45) + ((-54) - (-45)) * r) = -((
      441971285725702722769547738124999999934020029071067499999998233993317120925468749999999999999999999999999999999999999
      + 618770273473222329755643790499999999934020029071067499999997880791980545110562500000000000000000000000000000000000000 * r
      + 371265242314531930480693137149999999973608011628426999999998940395990272555281250000000000000000000000000000000000000 * r ^ 2
      + 123755482809783109917425751619999999994721602325685399999999717438930739348075000000000000000000000000000000000000000 * r ^ 3
      + 24751116249999999045871287580999999999472160232568539999999957615839610902211250000000000000000000000000000000000000 * r ^ 4
      + 2970133949999999999999999999999999999978886409302741599999996609267168872176900000000000000000000000000000000000000 * r ^ 5
      + 198008929999999999999999999999999999999999999999999999999999886975572295739230000000000000000000000000000000000000 * r ^ 6
      + 5657398000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * r ^ 7) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
    unfold Hpoly
    ring
  rw [hid]
  exact neg_nonpos.mpr (by positivity)
