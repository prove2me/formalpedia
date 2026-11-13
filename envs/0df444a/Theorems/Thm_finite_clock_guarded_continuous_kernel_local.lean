-- Prove2me | Theorems.Thm_finite_clock_guarded_continuous_kernel_local
-- name    : finite_clock_guarded_continuous_kernel_local
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T13:49:18.134325+00:00
-- url     : https://prove2.me/theorems/68e3a639-10f2-47ee-92b0-261b4088f578
-- title:
--   finite_clock_guarded_continuous_kernel_local
-- statement:
--   Automatically extracted helper theorem finite_clock_guarded_continuous_kernel_local from oversized parent candidate 993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de.
-- source:
--   candidate-decomposition:10ef35ab-e13b-45f3-9ed8-046c77d64038:993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem finite_clock_guarded_continuous_kernel_local
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (Y : ℝ≥0 → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0) :
    Integrable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0) μ := by sorry
end
