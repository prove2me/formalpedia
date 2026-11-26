-- Prove2me | Theorems.Thm_cap_kernel_le_of_bound
-- name    : cap_kernel_le_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:50.58981+00:00
-- url     : https://prove2.me/theorems/3b0044a6-e4b5-4808-b0bd-e883e7cdc28e
-- title:
--   cap kernel le of bound: cap kernel le of bound
-- statement:
--   (a) direction, pointwise: a bound `β` controlling all approximations
--       forces `c ≤ κ x (A_x)` (via the core lemma and continuity from above).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L485-L507
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L485-L507

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
omit [BorelSpace X]

theorem cap_kernel_le_of_bound
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) [IsFiniteKernel κ] {x : X} {c : ℝ≥0∞} {β : ℕ → ℕ}
    (h : ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n)) :
    c ≤ κ x (Prod.mk x ⁻¹' range π) := by sorry
