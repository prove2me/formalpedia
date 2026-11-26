-- Prove2me | Theorems.Thm_leftmostBranchG_mem
-- name    : leftmostBranchG_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:03.459429+00:00
-- url     : https://prove2.me/theorems/bd451be0-7fa4-4c0a-879d-153ae3fda645
-- title:
--   leftmost Branch G mem: leftmost Branch G mem
-- statement:
--   The leftmost Branch G mem construction uses the leftmost Branch G mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L98-L107
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L98-L107

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]

theorem leftmostBranchG_mem
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    (x, leftmostBranchG F x h₀) ∈ F := by sorry
