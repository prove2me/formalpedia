-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S7Proof_segment_g1_01
-- name    : Erdos1041.Counterexample.S7Proof.segment_g1_01
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:33:48.449389+00:00
-- url     : https://prove2.me/theorems/868b900c-13f4-4ceb-b8f7-2b11a5d64597
-- title:
--   Nonpositive barrier segment g1_01
-- statement:
--   For the closed rational segment 0≤r≤1 encoded by the exact rational endpoints in the formal statement, the barrier polynomial Hpoly is nonpositive at every parameter value. This is a certificate for the first separating graph.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierCertificates.lean#L246-L248
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

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

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open Erdos1041.Counterexample.S7Proof

theorem Erdos1041.Counterexample.S7Proof.segment_g1_01 (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Hpoly ((-25) + ((-11 / 2) - (-25)) * r) ((125 / 4) + ((61 / 10) - (125 / 4)) * r) ≤ 0 := by sorry
