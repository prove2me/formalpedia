-- Prove2me | Theorems.Thm_leftmostBranchG_least
-- name    : leftmostBranchG_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:59.288969+00:00
-- url     : https://prove2.me/theorems/c34005f8-b9cc-5605-a374-d5041158a18e
-- title:
--   leftmost Branch G least: leftmost Branch G least
-- statement:
--   The leftmost Branch G least construction uses the leftmost Branch G least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L110-L114
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Tree.lean#L110-L114

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

theorem leftmostBranchG_least (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n k : ℕ)
    (hk : k < leftmostBranchG F x h₀ n) :
    ¬(fiberRestNG F x (Function.update (leftmostAuxG F x h₀ n).val n k) (n + 1)).Nonempty := by sorry
