-- Prove2me | Theorems.Thm_thm_2_4_tendsto
-- name    : thm_2_4_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:21:23.954829+00:00
-- url     : https://prove2.me/theorems/13391957-9d8a-4dbc-934c-353d25128a0d
-- title:
--   Chapter 2, thm_2_4
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_4`: `thm_2_4_tendsto`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators

/--  # Theorem 2.4 Measure function is continuous from below

Explicit filter-limit form of Theorem 2.4. -/
theorem thm_2_4_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋃ i, A i))) := by
  sorry
