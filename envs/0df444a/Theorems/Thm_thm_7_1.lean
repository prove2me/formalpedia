-- Prove2me | Theorems.Thm_thm_7_1
-- name    : thm_7_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:56:34.718112+00:00
-- url     : https://prove2.me/theorems/e365721a-a400-4df8-8898-ca62ad356499
-- title:
--   Chapter 7, thm_7_1
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `thm_7_1`: `thm_7_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_1.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

/--
## Theorem 7.1: triangle inequality
for real- or complex-valued integrable
functions, the norm/absolute value of the integral
is bounded by the integral of the pointwise norm.

We use an existing API in Mathlib to finish the proof
-/
theorem thm_7_1 {Ω 𝕜 : Type*}
  [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
  (X : Ω → 𝕜) (_hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  sorry
