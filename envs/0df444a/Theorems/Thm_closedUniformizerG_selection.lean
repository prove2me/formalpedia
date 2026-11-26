-- Prove2me | Theorems.Thm_closedUniformizerG_selection
-- name    : closedUniformizerG_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:06.270145+00:00
-- url     : https://prove2.me/theorems/be25fe14-0b0f-40ca-a052-17199d28b0c4
-- title:
--   closed Uniformizer G selection: closed Uniformizer G selection
-- statement:
--   The closed Uniformizer G selection construction uses the closed Uniformizer G selection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L143-L148
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L143-L148

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

theorem closedUniformizerG_selection
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    {x : X} (hx : x ∈ Prod.fst '' F) :
    (x, closedUniformizerG F hF hne x) ∈ F := by sorry
