-- Prove2me | Theorems.Thm_capW_antitone
-- name    : capW_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:01:48.01037+00:00
-- url     : https://prove2.me/theorems/679281f6-26d0-4bd8-96de-5c1590f4acb0
-- title:
--   cap W antitone: cap W antitone
-- statement:
--   The cap W antitone construction uses the cap W antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L161-L168
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L161-L168

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

theorem capW_antitone (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) : Antitone (capW π β) := by sorry
