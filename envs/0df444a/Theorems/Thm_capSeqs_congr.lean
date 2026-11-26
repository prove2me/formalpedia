-- Prove2me | Theorems.Thm_capSeqs_congr
-- name    : capSeqs_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:23.328531+00:00
-- url     : https://prove2.me/theorems/cf4f1f0b-0caa-5fd7-829f-097b955d3993
-- title:
--   cap Seqs congr: cap Seqs congr
-- statement:
--   The cap Seqs congr construction uses the cap Seqs congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L118-L123
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L118-L123

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

theorem capSeqs_congr {β β' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, β i = β' i) :
    capSeqs β n = capSeqs β' n := by sorry
