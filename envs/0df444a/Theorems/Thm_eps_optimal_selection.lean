-- Prove2me | Theorems.Thm_eps_optimal_selection
-- name    : eps_optimal_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:11.122824+00:00
-- url     : https://prove2.me/theorems/12dac518-8eb5-5d7d-82ef-dce2ce564d29
-- title:
--   eps optimal selection: eps optimal selection
-- statement:
--   ε-optimal selection: for each a, choose m ∈ S(a) with f(a,m) ≤ inf + ε.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/JankovVonNeumann.lean#L35-L47
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/JankovVonNeumann.lean#L35-L47

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section

theorem eps_optimal_selection
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : α → Set (Measure β))
    (h_ne : ∀ a, (S a).Nonempty)
    (f : α → Measure β → ENNReal)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (sel : α → Measure β),
      (∀ a, sel a ∈ S a) ∧
      (∀ a, f a (sel a) ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε) := by sorry
