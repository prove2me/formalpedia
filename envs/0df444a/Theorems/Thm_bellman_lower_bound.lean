-- Prove2me | Theorems.Thm_bellman_lower_bound
-- name    : bellman_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:14.081223+00:00
-- url     : https://prove2.me/theorems/2c024b55-3891-48c4-9af7-53a3b98c4df4
-- title:
--   bellman lower bound: bellman lower bound
-- statement:
--   The bellman lower bound construction uses the bellman lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LowerBound.lean#L23-L32
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LowerBound.lean#L23-L32

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem bellman_lower_bound
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂kd.γ₀
    ≤ totalCost c₀ c₁ kd.γ₀ kd.γ₁ := by sorry
