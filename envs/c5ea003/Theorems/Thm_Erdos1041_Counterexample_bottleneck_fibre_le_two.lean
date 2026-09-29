-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_fibre_le_two
-- name    : Erdos1041.Counterexample.bottleneck_fibre_le_two
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:23.585894+00:00
-- url     : https://prove2.me/theorems/4dc2e381-183b-4344-98b7-8de554ecfc40
-- title:
--   The slit covering has at most two sheets
-- statement:
--   Let p(cc) be nonzero, assume the slit projection is a covering map, and suppose b₁ and b₂ are roots in cc’s strict-lemniscate component and every root in that component is one of them. If three points of the slit domain have the same projection, at least two are equal.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1075-L1143
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

theorem Erdos1041.Counterexample.bottleneck_fibre_le_two (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (e₁ e₂ e₃ : bottleneckSlitDomain p cc)
    (h12 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₂)
    (h13 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₃) :
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by sorry
