-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
-- name    : Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:31:05.200984+00:00
-- url     : https://prove2.me/theorems/7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5
-- title:
--   Proper local homeomorphisms are covering maps
-- statement:
--   For a Hausdorff source, any map that is both proper and a local homeomorphism is a covering map, allowing an empty fiber.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Components.lean#L19-L176
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

theorem Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {g : E → X} (hproper : IsProperMap g) (hlocal : IsLocalHomeomorph g) :
    IsCoveringMap g := by sorry
