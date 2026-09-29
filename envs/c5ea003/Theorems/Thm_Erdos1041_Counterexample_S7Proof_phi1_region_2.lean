-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S7Proof_phi1_region_2
-- name    : Erdos1041.Counterexample.S7Proof.phi1_region_2
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T23:10:59.065464+00:00
-- url     : https://prove2.me/theorems/25086e71-66b6-419b-805b-48063d4eacb7
-- title:
--   First graph barrier: upper middle branch
-- statement:
--   For x between 3615717603167/500000000000 and 519/10, the first piecewise barrier phi₁ equals l1_12.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierGraphs.lean#L112-L116
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

theorem Erdos1041.Counterexample.S7Proof.phi1_region_2 (x : ℝ) (hlo : (3615717603167 / 500000000000) ≤ x) (hhi : x ≤ (519 / 10)) :
    phi1 x = l1_12 x := by sorry
