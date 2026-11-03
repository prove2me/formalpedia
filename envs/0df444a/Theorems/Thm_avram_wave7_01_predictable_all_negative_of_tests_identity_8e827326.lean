-- Prove2me | Theorems.Thm_avram_wave7_01_predictable_all_negative_of_tests_identity_8e827326
-- name    : avram_wave7_01_predictable_all_negative_of_tests_identity_8e827326
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:01:06.745178+00:00
-- url     : https://prove2.me/theorems/c88ad958-6211-4c3f-a07c-9aa9696489c5
-- title:
--   Avram wave7 01 predictable all negative of tests: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem avram_wave7_01_predictable_all_negative_of_tests_identity_8e827326
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (D : Set ℝ) (hD : MeasurableSet D)
    (C : ℕ → Set ℝ) (hCm : ∀ n, MeasurableSet (C n))
    (hCmono : Monotone C) (hCover : (⋃ n, C n) = D)
    (hTests : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ ∧
      ∀ a : ℝ,
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) 
    (hSep : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε))
    : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C n) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (C n) := by sorry
