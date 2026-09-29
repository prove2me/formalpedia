-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_bottleneck_sublevel_isPreconnected
-- name    : Erdos1041.Counterexample.bottleneck_sublevel_isPreconnected
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:35.00702+00:00
-- url     : https://prove2.me/theorems/91e140d6-078c-4522-8dde-561e9bae92c2
-- title:
--   A bounded holomorphic sublevel is preconnected here
-- statement:
--   For a differentiable complex map on an open set, if its sublevel is bounded, its closure stays inside the domain, and it has one zero c in the domain, then the sublevel containing c is preconnected under the stated norm threshold.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L627-L697
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

theorem Erdos1041.Counterexample.bottleneck_sublevel_isPreconnected (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hdiff : DifferentiableOn ℂ f V) (c : ℂ) (hc : c ∈ V) (m : ℝ) (hm : ‖f c‖ < m)
    (hzero : ∀ z ∈ V, f z = 0 → z = c)
    (hbdd : Bornology.IsBounded {z | z ∈ V ∧ ‖f z‖ < m})
    (hcl : closure {z | z ∈ V ∧ ‖f z‖ < m} ⊆ V) :
    IsPreconnected {z | z ∈ V ∧ ‖f z‖ < m} := by sorry
