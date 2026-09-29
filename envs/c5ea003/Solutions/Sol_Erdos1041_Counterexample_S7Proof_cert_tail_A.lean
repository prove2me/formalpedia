-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.cert_tail_A
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:33:57.237416+00:00
-- url     : https://prove2.me/submissions/a8a0058c-2853-46bd-953f-54db21a834d1

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
    Hpoly ((-25) + ((-29) - (-25)) * r) ((125 / 4) + ((145 / 4) - (125 / 4)) * r) ≤ 0 := by
  have hid : Hpoly ((-25) + ((-29) - (-25)) * r) ((125 / 4) + ((145 / 4) - (125 / 4)) * r) = -((
      164401906390677567802891262023925781181092407447879791259767445585952452382445335388183593749999999999999999999999999
      + 184123386020263428718854887695312499944873925958303833007814247762514354287147521972656250000000000000000000000000000 * r
      + 88377539280058089518525173046874999982359656306657226562500699105005741714859008789062500000000000000000000000000000 * r ^ 2
      + 23567156756579267820642685124999999997177545009065156250000149142401224899169921875000000000000000000000000000000000 * r ^ 3
      + 3770737304687500312825707404999999999774203600725212500000017897088146987900390625000000000000000000000000000000000 * r ^ 4
      + 361990781249999999999999999999999999992774515223206800000001145413641407225625000000000000000000000000000000000000 * r ^ 5
      + 19306175000000000000000000000000000000000000000000000000000030544363770859350000000000000000000000000000000000000 * r ^ 6
      + 441284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 * r ^ 7) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
    unfold Hpoly
    ring
  rw [hid]
  exact neg_nonpos.mpr (by positivity)
