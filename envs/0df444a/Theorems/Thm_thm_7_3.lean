-- Prove2me | Theorems.Thm_thm_7_3
-- name    : thm_7_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:56:24.896841+00:00
-- url     : https://prove2.me/theorems/65feab2b-0782-423b-9b47-45fa538c00a0
-- title:
--   Chapter 7, thm_7_3
-- statement:
--   Supporting Lean declarations for Chapter 7, source module `thm_7_3`: `thm_7_3`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/thm_7_3.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory

/--  ## Theorem 7.4 Fatou lemma
Exported statement for Fatou's lemma in the textbook
nonnegative setting, modeled as an `ENNReal`-valued sequence.

We apply an equivalent API in Mathlib.
-/
theorem thm_7_3 {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : ℕ → Ω → ENNReal)
  (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop := by
  sorry
