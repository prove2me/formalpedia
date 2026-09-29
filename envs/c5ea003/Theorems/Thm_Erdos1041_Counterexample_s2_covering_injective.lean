-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s2_covering_injective
-- name    : Erdos1041.Counterexample.s2_covering_injective
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:31:20.313831+00:00
-- url     : https://prove2.me/theorems/0cf8b542-e000-478a-a36c-a2d119affc63
-- title:
--   A connected covering of a simply connected base is injective
-- statement:
--   A covering map from a preconnected space into a locally path-connected, simply connected space is injective; the statement adds no surjectivity requirement.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Components.lean#L178-L196
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
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
Formalisation of Lemma 2.1 from `ani_degree7_counterexample.tex`. -/

/-
Integration: move the S2 declaration out of Defs before importing this module.
The supplied Defs is preserved under input/; see DEFS_DELTAS.md.
Repaired and compiled against Mathlib v4.29.1 (commit 5e932f97).
-/

noncomputable section

open Set Filter Topology

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.s2_covering_injective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    {g : E → X} (hcover : IsCoveringMap g) : Function.Injective g := by sorry
