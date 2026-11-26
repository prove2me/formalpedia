-- Prove2me | Theorems.Thm_closedFiberG_nonempty_iff
-- name    : closedFiberG_nonempty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:33.102815+00:00
-- url     : https://prove2.me/theorems/c0d05392-a743-55c5-86a1-0d605418eab5
-- title:
--   closed Fiber G nonempty iff: closed Fiber G nonempty iff
-- statement:
--   The closed Fiber G nonempty iff construction uses the closed Fiber G nonempty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L27-L31
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L27-L31

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

theorem closedFiberG_nonempty_iff (F : Set (X × (ℕ → ℕ))) (x : X) :
    (closedFiberG F x).Nonempty ↔ x ∈ Prod.fst '' F := by sorry
