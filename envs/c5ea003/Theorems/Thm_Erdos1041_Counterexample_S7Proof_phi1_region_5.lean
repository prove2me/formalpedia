-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_5
-- name    : Erdos1041.Counterexample.S7Proof.phi1_region_5
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T23:12:57.107882+00:00
-- url     : https://prove2.me/theorems/49906de7-f655-4bf3-807a-c93ae27b3a0d
-- title:
--   First graph barrier: far negative branch
-- statement:
--   For x at most -224, the first piecewise barrier phi₁ equals -(3/14)x.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierGraphs.lean#L130-L134
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction.

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

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open Erdos1041.Counterexample.S7Proof

theorem Erdos1041.Counterexample.S7Proof.phi1_region_5 (x : ℝ) (hhi : x ≤ (-224)) :
    phi1 x = (-3 / 14) * x := by sorry
