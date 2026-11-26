-- Prove2me | Theorems.Thm_exists_fallback_selector
-- name    : exists_fallback_selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:31.329797+00:00
-- url     : https://prove2.me/theorems/a4b98723-8308-50eb-896c-af2b800f59bc
-- title:
--   exists fallback selector: exists fallback selector
-- statement:
--   A σ(Σ¹₁)-measurable everywhere-feasible selector exists as soon as the
--       graph is analytic, nonempty, and has nonempty fibers
--       (Jankov–von Neumann).
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L50-L57
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L50-L57

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]

theorem exists_fallback_selector [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} (hΓ : AnalyticSet Γ) (hΓne : Γ.Nonempty)
    (hfib : ∀ h : H, ∃ e : E, (h, e) ∈ Γ) :
    ∃ φ : H → E, AnalyticallyMeasurable φ ∧ ∀ h, (h, φ h) ∈ Γ := by sorry
