-- Prove2me | Theorems.Thm_fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d
-- name    : fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:44:30.100725+00:00
-- url     : https://prove2.me/theorems/f0347e01-c890-4d0e-8803-adfbd94898fb
-- title:
--   Fatou liminf nonmonotone: Pointwise upper bound
-- statement:
--   The same original-source expected discounted full Stieltjes dividend budget transfers from arbitrary measurable clocks tau_n to the dominated monotone tail-infimum clocks sigma_n. At each sample path sigma_n is no later than tau_n, so every stopped payment set is included in the original one, including time zero and arbitrary dividend singular/atomic mass. This is the source-faithful early-split helper from the non-monotone UBV Fatou proof; it does not assume or establish the underlying stochastic budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_ae_cofinal_stochastic_fatou_no_extra_nonneg
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem fatou_liminf_nonmonotone_pointwise_upper_bound_a302087d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) 
    (hσmeas : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n, Measurable (σ n)))
    (hσmono : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ ω, Monotone (fun n => σ n ω)))
    (hσsupAE : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ᵐ ω ∂P, (⨆ n, σ n ω) = ruinTime X x D ω))
    (hσle : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n ω, σ n ω ≤ τ n ω))
    : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨅ k : ℕ, τ (n + k) ω; ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by sorry
end
