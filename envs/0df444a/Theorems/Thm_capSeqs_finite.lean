-- Prove2me | Theorems.Thm_capSeqs_finite
-- name    : capSeqs_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:25.690893+00:00
-- url     : https://prove2.me/theorems/42152882-76f6-4db8-a937-9316c30e2451
-- title:
--   cap Seqs finite: cap Seqs finite
-- statement:
--   The cap Seqs finite construction uses the cap Seqs finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L103-L116
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L103-L116

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

theorem capSeqs_finite (β : ℕ → ℕ) (n : ℕ) : (capSeqs β n).Finite := by sorry
