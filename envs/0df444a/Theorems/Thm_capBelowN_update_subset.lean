-- Prove2me | Theorems.Thm_capBelowN_update_subset
-- name    : capBelowN_update_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:04:09.713951+00:00
-- url     : https://prove2.me/theorems/48868750-6d08-439a-9a2f-8dd8eba3f032
-- title:
--   cap Below N update subset: cap Below N update subset
-- statement:
--   The cap Below N update subset construction uses the cap Below N update subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L49-L53
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L49-L53

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

theorem capBelowN_update_subset (β : ℕ → ℕ) (n k : ℕ) :
    capBelowN (Function.update β n k) (n + 1) ⊆ capBelowN β n := by sorry
