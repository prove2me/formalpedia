-- Prove2me | Theorems.Thm_range_subset_capKernel
-- name    : range_subset_capKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:38.841174+00:00
-- url     : https://prove2.me/theorems/78d1d43f-ead2-4a79-95e0-06298a5182e5
-- title:
--   range subset cap Kernel: range subset cap Kernel
-- statement:
--   The range subset cap Kernel construction uses the range subset cap Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L273-L276
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L273-L276

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

theorem range_subset_capKernel (π : (ℕ → ℕ) → Z) : range π ⊆ capKernel π := by sorry
