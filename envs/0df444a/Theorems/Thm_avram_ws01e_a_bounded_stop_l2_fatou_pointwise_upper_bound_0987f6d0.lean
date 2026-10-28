-- Prove2me | Theorems.Thm_avram_ws01e_a_bounded_stop_l2_fatou_pointwise_upper_bound_0987f6d0
-- name    : avram_ws01e_a_bounded_stop_l2_fatou_pointwise_upper_bound_0987f6d0
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T15:11:47.372097+00:00
-- url     : https://prove2.me/theorems/c407cf7f-fb29-4709-be06-f1abb1e21e0f
-- title:
--   Avram ws01e a bounded stop l2 fatou: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem avram_ws01e_a_bounded_stop_l2_fatou_pointwise_upper_bound_0987f6d0
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n → s ≤ T)
    (hstop : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) 
    (hfmeas : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n, Measurable (f n)))
    (hpow : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n ω,
      (Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) ^ 2 =
      Real.exp ((2 * θ) * X.X (τn n ω) ω -
        2 * (τn n ω : ℝ) * X.ψ θ)))
    : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n, (∫⁻ ω, f n ω ∂P) ≤ C) := by sorry
