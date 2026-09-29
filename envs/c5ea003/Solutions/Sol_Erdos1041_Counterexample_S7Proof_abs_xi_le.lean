-- Prove2me | solution 1 for Erdos1041.Counterexample.S7Proof.abs_xi_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:30:05.484199+00:00
-- url     : https://prove2.me/submissions/c1997b33-7cba-4342-bfd7-403860bc9e59

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

/-!
The namespace `S7Proof` keeps the barrier lemmas separate from the shared
definitions in `Defs.lean`.  These lemmas are consumed by
`InstanceBarriers.lean` and belong to the successfully checked counterexample
dependency chain.
-/
noncomputable section

open scoped ComplexConjugate

namespace Erdos1041.Counterexample.S7Proof
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
end Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Erdos1041 in
open Erdos1041.Counterexample in
open Erdos1041.Counterexample.S7Proof in
theorem solution (z : ℂ) : |xi z| ≤ 9 * ‖z‖ := by
  have h1 := abs_le.mp (Complex.abs_re_le_norm z)
  have h2 := abs_le.mp (Complex.abs_im_le_norm z)
  rw [abs_le]
  unfold xi
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
