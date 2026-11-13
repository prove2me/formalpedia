-- Prove2me | Theorems.Thm_thm_5_10
-- name    : thm_5_10
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:49:56.676636+00:00
-- url     : https://prove2.me/theorems/ccfdea78-3907-4389-9017-643484b182b6
-- title:
--   Chapter 5, thm_5_10
-- statement:
--   Supporting Lean declarations for Chapter 5, source module `thm_5_10`: `thm_5_10`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_10.lean

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open Filter
open scoped ENNReal Topology

/-- ## Theorem 5.10 Borel's zero-one law
for independent measurable events in a probability space,
the probability of occurring infinitely often is
completely determined by whether the probability series
diverges or converges.
-/
theorem thm_5_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P) :
    P (limsup A atTop) = if (∑' n, P (A n)) = ∞ then 1 else 0 := by
  sorry
