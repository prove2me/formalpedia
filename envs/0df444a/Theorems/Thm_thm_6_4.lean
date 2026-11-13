-- Prove2me | Theorems.Thm_thm_6_4
-- name    : thm_6_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:56:17.401514+00:00
-- url     : https://prove2.me/theorems/b64d5cd1-1a27-4546-910f-1e1e3668d018
-- title:
--   Chapter 6, thm_6_4
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_4`: `thm_6_4`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_4.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Filter

/--
# Theorem 6.4 Monotone convergence theorem
for a monotone increasing sequence of nonnegative measurable
functions whose pointwise supremum is `X`, the integrals converge to the
integral of `X`.

The corresponding theorem in Mathlib is `lintegral_iSup`
-/
theorem thm_6_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ENNReal)
    (X : Ω → ENNReal) (h_meas : ∀ n, Measurable (Xn n)) (h_mono : Monotone Xn)
    (h_sup : ∀ ω, (⨆ n, Xn n ω) = X ω) :
    Tendsto (fun n => ∫⁻ ω, Xn n ω ∂μ) atTop (nhds (∫⁻ ω, X ω ∂μ)) := by
  sorry
