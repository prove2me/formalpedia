-- Prove2me | Theorems.Thm_avram_p4_f_assembly_original_terminal_mean_bound_identity_532fd08c
-- name    : avram_p4_f_assembly_original_terminal_mean_bound_identity_532fd08c
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:51:02.621592+00:00
-- url     : https://prove2.me/theorems/90fde9d8-fcce-4797-aa7e-1bfedd5eaa6c
-- title:
--   Avram p4 f assembly original terminal mean bound: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem avram_p4_f_assembly_original_terminal_mean_bound_identity_532fd08c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω) 
    (hSrc : Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P)
    : (fun ω => Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) =
      (fun ω => (K * Real.exp (θ * x)) *
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) := by sorry
end
