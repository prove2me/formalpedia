-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_S4Proofs_delta_le
-- name    : Erdos1041.Counterexample.S4Proofs.delta_le
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T20:20:08.904152+00:00
-- url     : https://prove2.me/theorems/3876d96d-8460-4c0e-8fa8-7a0a9f05c41c
-- title:
--   The critical-value deficit has an exact upper bound
-- statement:
--   At zs, the deficit 1−|f(zs)| is at most ρ⁷ε⁷(36/5)/10⁶.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceCritical.lean#L3639-L3658
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041.Counterexample.S4Proofs
noncomputable section
open scoped ComplexConjugate NNReal
noncomputable section
open scoped ComplexConjugate NNReal
set_option maxHeartbeats 4000000

open Erdos1041.Counterexample.S4Proofs

theorem Erdos1041.Counterexample.S4Proofs.delta_le : 1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) := by sorry
