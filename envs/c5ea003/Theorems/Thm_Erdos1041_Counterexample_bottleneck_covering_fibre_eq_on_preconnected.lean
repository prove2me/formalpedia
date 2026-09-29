-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_covering_fibre_eq_on_preconnected
-- name    : Erdos1041.Counterexample.bottleneck_covering_fibre_eq_on_preconnected
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:26:44.838195+00:00
-- url     : https://prove2.me/theorems/243aec71-47cd-40e8-b5c9-5e24cea97fe6
-- title:
--   Equal projections on a connected lift are equal
-- statement:
--   For a covering over a locally path-connected simply connected base, if a continuous map on a preconnected set has two points with equal projections, their lifted images are equal.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L332-L353
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

theorem Erdos1041.Counterexample.bottleneck_covering_fibre_eq_on_preconnected
    {E B T : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace B] [TopologicalSpace T]
    [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    (π : E → B) (hπ : IsCoveringMap π)
    (S : Set T) (hS : IsPreconnected S) (g : T → E) (hg : ContinuousOn g S)
    (a b : T) (ha : a ∈ S) (hb : b ∈ S) (hab : π (g a) = π (g b)) :
    g a = g b := by sorry
