-- Prove2me | Theorems.Thm_leftmostWitnessG_agrees
-- name    : leftmostWitnessG_agrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:33.914849+00:00
-- url     : https://prove2.me/theorems/15b5df1a-6eb4-5909-962e-17de83caaeea
-- title:
--   leftmost Witness G agrees: leftmost Witness G agrees
-- statement:
--   The leftmost Witness G agrees construction uses the leftmost Witness G agrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L93-L96
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L93-L96

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
omit [TopologicalSpace X]

theorem leftmostWitnessG_agrees (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n i) (hi : i < n) :
    leftmostWitnessG F x h₀ n i = leftmostBranchG F x h₀ i := by sorry
