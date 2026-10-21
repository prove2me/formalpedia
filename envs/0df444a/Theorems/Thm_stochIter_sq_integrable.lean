-- Prove2me | Theorems.Thm_stochIter_sq_integrable
-- name    : stochIter_sq_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:37:20.503436+00:00
-- url     : https://prove2.me/theorems/649e4625-a36d-4394-87a4-e717f2344609
-- title:
--   stochIter_sq_integrable
-- statement:
--   Automatically extracted helper theorem stochIter_sq_integrable from oversized parent candidate de37d2acb8f301155d7d44d38261b50b0896da704c8b2f588d0c7ea538d67db4.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:de37d2acb8f301155d7d44d38261b50b0896da704c8b2f588d0c7ea538d67db4

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem stochIter_sq_integrable {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n))
    (xstar : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (B : ℝ) (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hG_int : Integrable (G k) μ)
    (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ)
    (hx_meas : Measurable[(ℱ k : MeasurableSpace Ω)] (stochIter h G x₀ k)) :
    Integrable (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2) μ := by sorry
