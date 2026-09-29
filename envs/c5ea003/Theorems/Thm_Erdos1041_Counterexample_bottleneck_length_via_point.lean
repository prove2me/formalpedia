-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_length_via_point
-- name    : Erdos1041.Counterexample.bottleneck_length_via_point
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:40.861324+00:00
-- url     : https://prove2.me/theorems/499dd161-c93f-4f2e-bb60-a744aef2e9eb
-- title:
--   A path length pays for a visit near cc
-- statement:
--   For any path from b₁ to b₂ and any parameter τ in [0,1], its extended total variation is at least |b₁−cc|+|b₂−cc|−2|γ(τ)−cc|.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L277-L303
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
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

open Erdos1041
open Erdos1041.Counterexample
noncomputable section
open Topology

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.bottleneck_length_via_point (γ : ℝ → ℂ) (b₁ b₂ cc : ℂ)
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 2 * ‖γ τ - cc‖) ≤ pathLength γ := by sorry
