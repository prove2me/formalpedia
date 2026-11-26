-- Prove2me | Theorems.Thm_exists_measurable_selection
-- name    : exists_measurable_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:30.012873+00:00
-- url     : https://prove2.me/theorems/b5d98e01-13fb-4e79-a6a2-1dab4d205629
-- title:
--   exists measurable selection: exists measurable selection
-- statement:
--   **The Kuratowski–Ryll-Nardzewski measurable selection theorem** (single-selection
--   form): a multifunction `Φ` from a measurable space into a complete separable metric
--   space, with nonempty closed values, such that `{a | (Φ a ∩ U).Nonempty}` is measurable
--   for every open `U`, admits a Borel-measurable selection.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L243-L255
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean#L243-L255

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace

theorem exists_measurable_selection {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by sorry
