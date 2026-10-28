-- Prove2me | Theorems.Thm_avram_ws01e_a_bounded_stop_l2_fatou_measurability_4c35e8fe
-- name    : avram_ws01e_a_bounded_stop_l2_fatou_measurability_4c35e8fe
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T15:12:16.954087+00:00
-- url     : https://prove2.me/theorems/77cdf854-c55e-4e71-8811-d24496fb8fb2
-- title:
--   Avram ws01e a bounded stop l2 fatou: Measurability
-- statement:
--   The specified function or random variable is measurable under the theorem's hypotheses.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem avram_ws01e_a_bounded_stop_l2_fatou_measurability_4c35e8fe
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
    : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); ∀ n, Measurable (f n)) := by sorry
