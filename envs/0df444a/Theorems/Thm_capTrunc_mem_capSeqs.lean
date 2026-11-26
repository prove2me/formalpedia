-- Prove2me | Theorems.Thm_capTrunc_mem_capSeqs
-- name    : capTrunc_mem_capSeqs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:41.193522+00:00
-- url     : https://prove2.me/theorems/c640e808-c057-4863-8156-0f707defe101
-- title:
--   cap Trunc mem cap Seqs: cap Trunc mem cap Seqs
-- statement:
--   The cap Trunc mem cap Seqs construction uses the cap Trunc mem cap Seqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L96-L101
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L96-L101

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

theorem capTrunc_mem_capSeqs {β : ℕ → ℕ} {n : ℕ} {σ : ℕ → ℕ}
    (h : σ ∈ capBelowN β n) : capTrunc σ n ∈ capSeqs β n := by sorry
