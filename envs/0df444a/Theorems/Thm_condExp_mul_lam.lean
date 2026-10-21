-- Prove2me | Theorems.Thm_condExp_mul_lam
-- name    : condExp_mul_lam
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T18:54:15.363049+00:00
-- url     : https://prove2.me/theorems/32b1594a-9202-4d39-9f91-36b97bee2daf
-- title:
--   Conditional expectation of a pointwise product, in lambda form
-- statement:
--   Conditional expectation of a pointwise lam of two real-valued functions, stated in the lambda form `μ[fun ω => f ω + g ω | m]`: the conditional expectation of the pointwise function sum is the pointwise sum of the conditional expectations.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:08f565cbc229a90ee96eb0aeeee6890c2b96e36a6af3a9ee953227573b23522e

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

theorem condExp_mul_lam {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by sorry
