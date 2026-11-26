-- Prove2me | Theorems.Thm_kernel_decomp_implies_bicausal
-- name    : kernel_decomp_implies_bicausal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:10.310282+00:00
-- url     : https://prove2.me/theorems/8c2be905-c456-5be3-940c-5131f696a487
-- title:
--   kernel decomp implies bicausal: kernel decomp implies bicausal
-- statement:
--   The kernel decomp implies bicausal construction uses the kernel decomp implies bicausal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Proposition1.lean#L14-L22
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Proposition1.lean#L14-L22

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_Proposition1
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]

theorem kernel_decomp_implies_bicausal
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_coupling : kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π := by sorry
