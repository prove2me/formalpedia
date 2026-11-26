-- Prove2me | Theorems.Thm_closedUniformizerG_cylinder_measurable
-- name    : closedUniformizerG_cylinder_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:11.18948+00:00
-- url     : https://prove2.me/theorems/104f78af-716f-5b9f-83cc-dfb35329e2eb
-- title:
--   closed Uniformizer G cylinder measurable: closed Uniformizer G cylinder measurable
-- statement:
--   The closed Uniformizer G cylinder measurable construction uses the closed Uniformizer G cylinder measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L224-L245
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L224-L245

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

theorem closedUniformizerG_cylinder_measurable [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    @MeasurableSet _ (analyticMeasurableSpace X)
      { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } := by sorry
