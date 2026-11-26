-- Prove2me | Theorems.Thm_leftmostAuxG_eq
-- name    : leftmostAuxG_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:37.352337+00:00
-- url     : https://prove2.me/theorems/4349935d-623d-4816-914d-50e512243bde
-- title:
--   leftmost Aux G eq: leftmost Aux G eq
-- statement:
--   The leftmost Aux G eq construction uses the leftmost Aux G eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L71-L81
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L71-L81

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

theorem leftmostAuxG_eq (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    ∀ n i, i < n → (leftmostAuxG F x h₀ n).val i = leftmostBranchG F x h₀ i := by sorry
