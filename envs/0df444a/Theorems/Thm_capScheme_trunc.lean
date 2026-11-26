-- Prove2me | Theorems.Thm_capScheme_trunc
-- name    : capScheme_trunc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:42.870333+00:00
-- url     : https://prove2.me/theorems/9f9c0ab0-f83b-5d50-b41c-66d91bcb1383
-- title:
--   cap Scheme trunc: cap Scheme trunc
-- statement:
--   The cap Scheme trunc construction uses the cap Scheme trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L148-L150
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L148-L150

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

theorem capScheme_trunc (π : (ℕ → ℕ) → Z) (σ : ℕ → ℕ) (n : ℕ) :
    capScheme π (capTrunc σ n) n = capScheme π σ n := by sorry
