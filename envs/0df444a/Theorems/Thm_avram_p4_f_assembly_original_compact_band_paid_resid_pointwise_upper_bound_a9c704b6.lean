-- Prove2me | Theorems.Thm_avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6
-- name    : avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:04:33.019565+00:00
-- url     : https://prove2.me/theorems/5bd4d66c-d019-4eef-aad0-580d2de9dfcb
-- title:
--   Avram p4 f assembly original compact band paid residual: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (u : ℝ≥0),
      (u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D u ω - D u ω ≤
        w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨
      (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPreBand : ∀ i : ι,
      riskProcess X x D (t i) ω ∈ Icc a b)
    (hPostBand : ∀ i : ι,
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b)
    (hPayNonneg : ∀ i : ι,
      0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) 
    : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
      max 1 (K : ℝ) * (rightLimit D (t i) ω - D (t i) ω) := by sorry
end
