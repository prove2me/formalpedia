-- Prove2me | Theorems.Thm_isCompact_capBelow
-- name    : isCompact_capBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:51.766921+00:00
-- url     : https://prove2.me/theorems/347ce877-a03d-4d78-9ccd-3e1f888a96ef
-- title:
--   is Compact cap Below: is Compact cap Below
-- statement:
--   The is Compact cap Below construction uses the is Compact cap Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L85-L87
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L85-L87

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

theorem isCompact_capBelow (β : ℕ → ℕ) : IsCompact (capBelow β) := by sorry
