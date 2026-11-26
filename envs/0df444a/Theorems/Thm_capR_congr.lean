-- Prove2me | Theorems.Thm_capR_congr
-- name    : capR_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:31.832474+00:00
-- url     : https://prove2.me/theorems/be37de45-dc83-5090-806e-b16bdf1fe0b5
-- title:
--   cap R congr: cap R congr
-- statement:
--   The cap R congr construction uses the cap R congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L250-L253
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L250-L253

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

theorem capR_congr (π : (ℕ → ℕ) → Z) {β β' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, β i = β' i) : capR π β n = capR π β' n := by sorry
