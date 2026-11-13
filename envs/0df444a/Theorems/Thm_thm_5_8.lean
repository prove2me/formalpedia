-- Prove2me | Theorems.Thm_thm_5_8
-- name    : thm_5_8
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:50:51.757101+00:00
-- url     : https://prove2.me/theorems/7ec67e80-dab4-45c0-ab3a-aa4ee1ecd426
-- title:
--   Chapter 5, thm_5_8
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_8`: `thm_5_8`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_8.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_8_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology

/-- ## Theorem 5.8 BC lemma 1
Borel-Cantelli Lemma 1: if the series of the probabilities of the events `A n`
is summable in `ℝ≥0∞`, then the limsup event has probability zero.

We keep the textbook shape by stating the result for a sequence of events in a
probability space, while delegating the technical proof to Mathlib's
`MeasureTheory.measure_limsup_atTop_eq_zero`.
-/
theorem thm_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_series : (∑' n, P (A n)) ≠ ∞) :
    P (limsup A atTop) = 0 := by
  sorry
