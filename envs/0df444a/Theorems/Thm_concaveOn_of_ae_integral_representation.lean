-- Prove2me | Theorems.Thm_concaveOn_of_ae_integral_representation
-- name    : concaveOn_of_ae_integral_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:48:34.057139+00:00
-- url     : https://prove2.me/theorems/d4356b06-1318-4fef-989f-5367ffdacc6b
-- title:
--   concaveOn_of_ae_integral_representation
-- statement:
--   Automatically extracted helper theorem concaveOn_of_ae_integral_representation from oversized parent candidate 59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17.
-- source:
--   candidate-decomposition:4204a6a5-95d4-4ce8-a739-2e52d3e9523a:59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem concaveOn_of_ae_integral_representation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (F : ℝ → ℝ) (g : Y → ℝ → ℝ)
    (hF : ∀ x, 0 ≤ x → F x = ∫ y, g y x ∂μ)
    (hconcave : ∀ᵐ y ∂μ, ConcaveOn ℝ (Set.Ici 0) (g y))
    (hint : ∀ x, 0 ≤ x → Integrable (fun y => g y x) μ) :
    ConcaveOn ℝ (Set.Ici 0) F := by sorry
