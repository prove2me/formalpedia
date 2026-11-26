-- Prove2me | Theorems.Thm_jvn_closedG
-- name    : jvn_closedG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:15.519803+00:00
-- url     : https://prove2.me/theorems/09059d76-8681-52a5-8da9-acdaa3159e99
-- title:
--   jvn closed G: jvn closed G
-- statement:
--   The jvn closed G construction uses the jvn closed G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L270-L276
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L270-L276

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

theorem jvn_closedG [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    ∃ (φ : X → (ℕ → ℕ)), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' F, (x, φ x) ∈ F := by sorry
