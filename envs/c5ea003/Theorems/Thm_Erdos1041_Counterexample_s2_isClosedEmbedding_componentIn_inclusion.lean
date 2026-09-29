-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s2_isClosedEmbedding_componentIn_inclusion
-- name    : Erdos1041.Counterexample.s2_isClosedEmbedding_componentIn_inclusion
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:27:19.405331+00:00
-- url     : https://prove2.me/theorems/6540821c-c137-474c-a360-69f63ed06c49
-- title:
--   A connected component embeds as a closed subspace
-- statement:
--   For any point z of a set S in a topological space, inclusion of the connected component of z in S into the ambient space is a closed embedding.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Components.lean#L198-L223
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

theorem Erdos1041.Counterexample.s2_isClosedEmbedding_componentIn_inclusion
    {E : Type*} [TopologicalSpace E] {S : Set E} {z : E} (hz : z ∈ S) :
    IsClosedEmbedding (Set.inclusion (connectedComponentIn_subset S z)) := by sorry
