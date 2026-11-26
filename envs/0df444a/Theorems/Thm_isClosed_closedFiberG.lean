-- Prove2me | Theorems.Thm_isClosed_closedFiberG
-- name    : isClosed_closedFiberG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:31.908272+00:00
-- url     : https://prove2.me/theorems/bf9e2c49-9f41-5571-80b5-8fd27cda3425
-- title:
--   is Closed closed Fiber G: is Closed closed Fiber G
-- statement:
--   The is Closed closed Fiber G construction uses the is Closed closed Fiber G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L33-L35
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L33-L35

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

theorem isClosed_closedFiberG {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X) :
    IsClosed (closedFiberG F x) := by sorry
