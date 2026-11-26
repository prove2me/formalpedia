-- Prove2me | Theorems.Thm_eps_optimal_kernel_bound
-- name    : eps_optimal_kernel_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:32.924249+00:00
-- url     : https://prove2.me/theorems/fa964cea-ccf8-5436-b3d9-cfc562829af2
-- title:
--   eps optimal kernel bound: eps optimal kernel bound
-- statement:
--   The eps optimal kernel bound construction uses the eps optimal kernel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L30-L42
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean#L30-L42

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem eps_optimal_kernel_bound
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_ne : ∀ z₀ : X₀ × Y₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)),
      (∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) ∧
      ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
        ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
            ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε := by sorry
