-- Prove2me | Theorems.Thm_thm_5_9
-- name    : thm_5_9
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:56:10.576658+00:00
-- url     : https://prove2.me/theorems/935b5c58-d660-4e72-986e-13318452f4a1
-- title:
--   Chapter 5, thm_5_9
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_9`: `thm_5_9`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_9.lean

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology

/--  ## Theorem 5.9 Borel-Cantelli Lemma 2
for independent measurable events in a probability
space, divergence of the probability series forces the limsup event to have
probability one.

We keep the statement at the event level and use Mathlib's
`ProbabilityTheory.measure_limsup_eq_one` for the proof.
-/
theorem thm_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P)
    (h_series : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 := by
  sorry
