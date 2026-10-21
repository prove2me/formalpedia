-- Prove2me | Theorems.Thm_condExp_mul_lam_f
-- name    : condExp_mul_lam_f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T19:26:26.261577+00:00
-- url     : https://prove2.me/theorems/4cca3418-7b3c-48b0-a0df-2c777ee6bfb8
-- title:
--   Conditional expectation of a pointwise product, in lambda form
-- statement:
--   Conditional expectation of a pointwise product of two real-valued functions, stated in the lambda form: the conditional expectation of the pointwise product is the pointwise product of the conditional expectations. For the product, the strong measurability of the left factor is taken for the conditioning measurable space.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:08f565cbc229a90ee96eb0aeeee6890c2b96e36a6af3a9ee953227573b23522e

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem condExp_mul_lam_f {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by sorry
