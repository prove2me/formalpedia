-- Prove2me | Theorems.Thm_bellman_value_geq
-- name    : bellman_value_geq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T07:59:47.740344+00:00
-- url     : https://prove2.me/theorems/7ebd16cb-3d4e-5495-a412-c1e50c940257
-- title:
--   bellman value geq: bellman value geq
-- statement:
--   The bellman value geq construction uses the bellman value geq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/ValueRepresentation.lean#L19-L35
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/ValueRepresentation.lean#L19-L35

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_ValueRepresentation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)

theorem bellman_value_geq
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀
    ≤ ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁ := by sorry
