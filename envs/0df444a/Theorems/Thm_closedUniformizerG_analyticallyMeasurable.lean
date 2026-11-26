-- Prove2me | Theorems.Thm_closedUniformizerG_analyticallyMeasurable
-- name    : closedUniformizerG_analyticallyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:09.977497+00:00
-- url     : https://prove2.me/theorems/16f5e27e-cabf-520e-bcf2-50b4c43e0572
-- title:
--   closed Uniformizer G analytically Measurable: closed Uniformizer G analytically Measurable
-- statement:
--   The closed Uniformizer G analytically Measurable construction uses the closed Uniformizer G analytically Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L249-L266
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L249-L266

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

theorem closedUniformizerG_analyticallyMeasurable [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    AnalyticallyMeasurable (closedUniformizerG F hF hne) := by sorry
