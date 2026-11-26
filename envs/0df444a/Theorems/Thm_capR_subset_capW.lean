-- Prove2me | Theorems.Thm_capR_subset_capW
-- name    : capR_subset_capW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:36.409157+00:00
-- url     : https://prove2.me/theorems/c998f837-8f6a-4ddc-b471-277b48d92f63
-- title:
--   cap R subset cap W: cap R subset cap W
-- statement:
--   The cap R subset cap W construction uses the cap R subset cap W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L265-L271
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L265-L271

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

theorem capR_subset_capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    capR π β n ⊆ capW π β n := by sorry
