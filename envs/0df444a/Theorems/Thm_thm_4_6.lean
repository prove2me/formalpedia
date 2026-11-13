-- Prove2me | Theorems.Thm_thm_4_6
-- name    : thm_4_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:49:48.137853+00:00
-- url     : https://prove2.me/theorems/a9423569-7a61-4eef-bae8-a264e72f31a1
-- title:
--   Chapter 4, thm_4_6
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `thm_4_6`: `thm_4_6`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_6.lean

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

theorem thm_4_6 {Ω : Type _} [MeasurableSpace Ω] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧ Measurable (f - g) ∧ (∀ c : ℝ, Measurable (c • f)) ∧ ((∀ ω, g ω ≠ 0) → Measurable (f / g)) := by
  sorry
