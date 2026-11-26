-- Prove2me | Theorems.Thm_bicausal_implies_decomp
-- name    : bicausal_implies_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:13.350811+00:00
-- url     : https://prove2.me/theorems/8ab81e57-5fc5-54ab-bf2c-f042734caa65
-- title:
--   bicausal implies decomp: bicausal implies decomp
-- statement:
--   The bicausal implies decomp construction uses the bicausal implies decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Proposition1.lean#L24-L33
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Proposition1.lean#L24-L33

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_Proposition1
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

theorem bicausal_implies_decomp
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (hbc : IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π) :
    ∃ (kd : KernelDecomp π),
      kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀ := by sorry
