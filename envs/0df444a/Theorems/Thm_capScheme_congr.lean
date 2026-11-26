-- Prove2me | Theorems.Thm_capScheme_congr
-- name    : capScheme_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:32.274423+00:00
-- url     : https://prove2.me/theorems/ca0cd0f0-f397-4798-b165-cb9c16ab89ae
-- title:
--   cap Scheme congr: cap Scheme congr
-- statement:
--   The cap Scheme congr construction uses the cap Scheme congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L137-L146
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L137-L146

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

theorem capScheme_congr (π : (ℕ → ℕ) → Z) {f g : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, f i = g i) : capScheme π f n = capScheme π g n := by sorry
