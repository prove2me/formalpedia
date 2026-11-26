-- Prove2me | Theorems.Thm_cap_kernel_exists_bound
-- name    : cap_kernel_exists_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:48.646988+00:00
-- url     : https://prove2.me/theorems/0fd35ca5-2894-4b24-90a2-ba16bc01e28a
-- title:
--   cap kernel exists bound: cap kernel exists bound
-- statement:
--   (b) direction, pointwise: from `c < κ x (A_x)` produce a bound `β`
--       controlling all bounded approximations.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L467-L480
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L467-L480

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
omit [BorelSpace X] [BorelSpace Y]

theorem cap_kernel_exists_bound
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) {x : X} {c : ℝ≥0∞}
    (hc : c < κ x (Prod.mk x ⁻¹' range π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n) := by sorry
