-- Prove2me | Theorems.Thm_exists_level_selector
-- name    : exists_level_selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:47.240224+00:00
-- url     : https://prove2.me/theorems/f380f516-ab53-5e62-981f-7147477ed65a
-- title:
--   exists level selector: exists level selector
-- statement:
--   Level selector at a constant threshold `q`: a σ(Σ¹₁)-measurable map
--       that, wherever the fiber meets the strict sublevel set `{F < q}`,
--       selects a feasible element below `q`; elsewhere it falls back to the
--       given selector `φ'`. The selection set `Γ ∩ {F < q}` is analytic, so
--       Jankov–von Neumann applies — this is the only place selection ever
--       happens, and the threshold is constant by design.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L65-L77
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean#L65-L77

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]

theorem exists_level_selector [PolishSpace H] [PolishSpace E]
    {Γ : Set (H × E)} {F : H × E → ℝ≥0∞}
    (hΓ : AnalyticSet Γ) (hF : IsLowerSemianalytic (X := H × E) F)
    {φ' : H → E} (hφ' : AnalyticallyMeasurable φ') (q : ℝ≥0∞) :
    ∃ χ : H → E, AnalyticallyMeasurable χ ∧
      ∀ h : H, (∃ e, (h, e) ∈ Γ ∧ F (h, e) < q) →
        (h, χ h) ∈ Γ ∧ F (h, χ h) < q := by sorry
