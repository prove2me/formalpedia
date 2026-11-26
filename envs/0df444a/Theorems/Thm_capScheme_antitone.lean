-- Prove2me | Theorems.Thm_capScheme_antitone
-- name    : capScheme_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:34.367897+00:00
-- url     : https://prove2.me/theorems/4e2619d1-f470-46c7-96ab-0ca5d4112c03
-- title:
--   cap Scheme antitone: cap Scheme antitone
-- statement:
--   The cap Scheme antitone construction uses the cap Scheme antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L133-L135
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L133-L135

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

theorem capScheme_antitone (π : (ℕ → ℕ) → Z) (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    capScheme π f n ⊆ capScheme π f m := by sorry
