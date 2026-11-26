-- Prove2me | Theorems.Thm_capBelow_eq_pi
-- name    : capBelow_eq_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:23.663795+00:00
-- url     : https://prove2.me/theorems/adb59392-59a3-4242-b02c-b2a3e3d4fc39
-- title:
--   cap Below eq pi: cap Below eq pi
-- statement:
--   The cap Below eq pi construction uses the cap Below eq pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L81-L83
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/Capacitability.lean#L81-L83

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

theorem capBelow_eq_pi (β : ℕ → ℕ) :
    capBelow β = Set.pi univ (fun i => Iic (β i)) := by sorry
