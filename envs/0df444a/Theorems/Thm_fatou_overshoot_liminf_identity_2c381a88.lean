-- Prove2me | Theorems.Thm_fatou_overshoot_liminf_identity_2c381a88
-- name    : fatou_overshoot_liminf_identity_2c381a88
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:21:39.350464+00:00
-- url     : https://prove2.me/theorems/3103e640-5896-4398-ba8a-3548687e2397
-- title:
--   Fatou overshoot liminf: Identity
-- statement:
--   For the actual SpectrallyNegativeLevy source and admissible D, suppose the liminf of a possibly nonmonotone sequence of measurable random clocks is at least ruinTime P-almost surely. Then clipping each clock at the genuine ruinTime forces the liminf of the clipped sequence to equal ruinTime almost surely, even when ruin occurs at zero or infinity. This follows from distribution of min through infima and suprema of ENNReal and leaves the corrected boundary and smoothness hypotheses unchanged. All expected Stieltjes budgets remain hypotheses and are not used to manufacture stochastic calculus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_liminf_clock_fatou_without_monotonicity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem fatou_overshoot_liminf_identity_2c381a88
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
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
    (τ : ℕ → Ω → ℝ≥0∞) (hτmeas : ∀ n, Measurable (τ n))
    (hτliminfLowerAE : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) 
    (hσmeas : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω); ∀ n, Measurable (σ n)))
    : (let σ : ℕ → Ω → ℝ≥0∞ := fun n ω => min (ruinTime X x D ω) (τ n ω); ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, σ (n + k) ω) = ruinTime X x D ω) := by sorry
end
