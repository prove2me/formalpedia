-- Prove2me | Theorems.Thm_optimal_kernel_exists_pointwise
-- name    : optimal_kernel_exists_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:34.217642+00:00
-- url     : https://prove2.me/theorems/9f9fb9cd-b77a-47f0-a1a5-277de91f74bf
-- title:
--   optimal kernel exists pointwise: optimal kernel exists pointwise
-- statement:
--   The optimal kernel exists pointwise construction uses the optimal kernel exists pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Existence.lean#L18-L32
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Existence.lean#L18-L32

import Definitions.Def_BicausalOT_Defs
import Mathlib.Topology.Semicontinuity.Basic
import Definitions.Def_BicausalOT_Existence
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
set_option linter.unusedSectionVars false

theorem optimal_kernel_exists_pointwise
    [TopologicalSpace (Measure (X₁ × Y₁))]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀)
    (h_ne : (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_compact : IsCompact (FeasibleSet₀ κ_μ κ_ν z₀ :
        Set (Measure (X₁ × Y₁))))
    (h_lsc : LowerSemicontinuousOn
        (fun γ : Measure (X₁ × Y₁) => ∫⁻ z₁, c₁ (z₀, z₁) ∂γ)
        (FeasibleSet₀ κ_μ κ_ν z₀)) :
    ∃ γ_star ∈ FeasibleSet₀ κ_μ κ_ν z₀,
      ∀ γ ∈ FeasibleSet₀ κ_μ κ_ν z₀,
        ∫⁻ z₁, c₁ (z₀, z₁) ∂γ_star ≤ ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by sorry
