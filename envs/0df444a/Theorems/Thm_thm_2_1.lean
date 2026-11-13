-- Prove2me | Theorems.Thm_thm_2_1
-- name    : thm_2_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:24:36.340005+00:00
-- url     : https://prove2.me/theorems/30d62f9c-6883-4afe-8135-3e126936405f
-- title:
--   Chapter 2, thm_2_1
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_1`: `thm_2_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_1.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic

open Set

/-- Exported statement for Theorem 2.1. -/
theorem thm_2_1 {Ω : Type*} (E : ℕ → Set Ω) :
    (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) ∧
      (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  sorry
