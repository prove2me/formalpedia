-- Prove2me | Theorems.Thm_conditional_one_step_expansion
-- name    : conditional_one_step_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:11:35.386929+00:00
-- url     : https://prove2.me/theorems/fcd32f89-ba9c-4ba0-b262-f0f3be65f672
-- title:
--   conditional_one_step_expansion
-- statement:
--   Automatically extracted helper theorem conditional_one_step_expansion from oversized parent candidate 1c8fc87901d45c876165f63b940f4247b4c683218af2ba3d2c2af72cb5e6623b.
-- source:
--   candidate-decomposition:e28554ec-8aa4-49db-8e89-83a73f8c4c8d:1c8fc87901d45c876165f63b940f4247b4c683218af2ba3d2c2af72cb5e6623b

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_stochIter_measurable_of_stronglyMeasurable
import Theorems.Thm_stochIter_sq_integrable
import Theorems.Thm_condExp_add_lam_g
import Theorems.Thm_condExp_sub_lam_g
import Theorems.Thm_condExp_mul_lam_g
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic

theorem conditional_one_step_expansion {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (xstar : EuclideanSpace ℝ (Fin n)) (B : ℝ)
    (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ)
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j))
    (hFil_le : (ℱ k : MeasurableSpace Ω) ≤ m0)
    (hdx : Measurable[(ℱ k : MeasurableSpace Ω)] (fun ω => stochIter h G x₀ k ω - xstar))
    (hinner : Integrable (fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ)
    (hinner_pull : μ[fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ | ℱ k]
        =ᵐ[μ] fun ω => ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ) :
    μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k]
        =ᵐ[μ] fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2
          - 2 * (h k (stochIter h G x₀ k ω)
              * ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ)
          + (h k (stochIter h G x₀ k ω)) ^ 2
            * (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω := by sorry
