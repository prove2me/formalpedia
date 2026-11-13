-- Prove2me | Theorems.Thm_thm_7_11
-- name    : thm_7_11
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:07.882419+00:00
-- url     : https://prove2.me/theorems/ddfaca00-378f-451e-8011-7db5cca29020
-- title:
--   Chapter 7, thm_7_11
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `thm_7_11`: `thm_7_11`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_11.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

/--
  ## Theorem 7.11
for a measurable `X : Ω → ℝ`, integrability of `h ∘ X` under
`μ` is equivalent to integrability of `h` under the pushforward
measure `Measure.map X μ`, and the corresponding integrals agree.
-/
theorem thm_7_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  sorry
