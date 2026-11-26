-- Prove2me | Theorems.Thm_capBelowN_congr
-- name    : capBelowN_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:16.714846+00:00
-- url     : https://prove2.me/theorems/fc1d28b9-effc-4aa6-a824-4d4fa0d1e969
-- title:
--   cap Below N congr: cap Below N congr
-- statement:
--   The cap Below N congr construction uses the cap Below N congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L43-L47
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L43-L47

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

theorem capBelowN_congr {β β' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, β i = β' i) :
    capBelowN β n = capBelowN β' n := by sorry
