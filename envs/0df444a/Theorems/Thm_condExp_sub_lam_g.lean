-- Prove2me | Theorems.Thm_condExp_sub_lam_g
-- name    : condExp_sub_lam_g
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T19:40:41.136095+00:00
-- url     : https://prove2.me/theorems/6d328e24-91a9-47e7-8625-190a7349c056
-- title:
--   Conditional expectation of a pointwise difference, in lambda form
-- statement:
--   Conditional expectation of a pointwise difference of two real-valued functions, stated in the lambda form: the conditional expectation of the pointwise difference is the pointwise difference of the conditional expectations. The conditioning measurable space and the measure's measurable space are separate parameters, as for `MeasureTheory.condExp`.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:08f565cbc229a90ee96eb0aeeee6890c2b96e36a6af3a9ee953227573b23522e

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem condExp_sub_lam_g {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by sorry
