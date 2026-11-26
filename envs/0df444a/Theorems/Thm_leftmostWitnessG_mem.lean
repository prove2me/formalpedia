-- Prove2me | Theorems.Thm_leftmostWitnessG_mem
-- name    : leftmostWitnessG_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:41.165934+00:00
-- url     : https://prove2.me/theorems/02457252-a7bb-40a4-9e48-d6ca452760ed
-- title:
--   leftmost Witness G mem: leftmost Witness G mem
-- statement:
--   The leftmost Witness G mem construction uses the leftmost Witness G mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L88-L90
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L88-L90

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

theorem leftmostWitnessG_mem (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n) :
    leftmostWitnessG F x h₀ n ∈ closedFiberG F x := by sorry
