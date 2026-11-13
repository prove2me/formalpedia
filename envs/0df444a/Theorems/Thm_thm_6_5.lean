-- Prove2me | Theorems.Thm_thm_6_5
-- name    : thm_6_5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:50:58.3262+00:00
-- url     : https://prove2.me/theorems/b21e2211-452b-4a4c-955d-11f789677f74
-- title:
--   Chapter 6, thm_6_5
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_5`: `thm_6_5`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_5.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory

/-- ## Theorem 6.5: linearity of the Lebesgue integral for nonnegative measurable functions.

We prove this using existing theorems in Mathlib
-/
theorem thm_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hX : Measurable X) (_hY : Measurable Y) (c : ENNReal) :
    ∫⁻ ω, X ω + Y ω ∂μ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ ∧
      ∫⁻ ω, c * X ω ∂μ = c * ∫⁻ ω, X ω ∂μ := by
  sorry
