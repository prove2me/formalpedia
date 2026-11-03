-- Prove2me | Theorems.Thm_avram_wave7_03_finite_clock_sup_fmono_f849371c
-- name    : avram_wave7_03_finite_clock_sup_fmono_f849371c
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:50:53.329437+00:00
-- url     : https://prove2.me/theorems/bd19586f-170d-48a5-8166-a78ee126e88e
-- title:
--   Avram wave7 03 finite clock sup: Auxiliary result
-- statement:
--   Under the explicitly listed hypotheses, the assertion in the formal Lean theorem statement holds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section
theorem avram_wave7_03_finite_clock_sup_fmono_f849371c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) 
    (hDiv : (let θ : ℕ → Ω → ℝ≥0 := ( fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))); let F : ℕ → Ω → ℝ≥0∞ := (fun n ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)); IsDividendStrategy 𝓕 D))
    (hθMeas : (let θ : ℕ → Ω → ℝ≥0 := ( fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))); let F : ℕ → Ω → ℝ≥0∞ := (fun n ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)); (∀ (n : ℕ), Measurable (fun ω => (θ n ω : ℝ)))))
    (hFm : (let θ : ℕ → Ω → ℝ≥0 := ( fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))); let F : ℕ → Ω → ℝ≥0∞ := (fun n ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)); (∀ (n : ℕ), Measurable (F n))))
    : (let θ : ℕ → Ω → ℝ≥0 := ( fun n ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))); let F : ℕ → Ω → ℝ≥0∞ := (fun n ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ n ω : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)); Monotone F) := by sorry
end
