-- Prove2me | Theorems.Thm_thm_2_1_part1
-- name    : thm_2_1_part1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:24:02.916387+00:00
-- url     : https://prove2.me/theorems/0c4e59f9-2de9-4ea8-a8ca-7ffce4bb7f23
-- title:
--   Chapter 2, thm_2_1
-- statement:
--   Supporting Lean declarations for Chapter 2, source module `thm_2_1`: `thm_2_1_part1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_1.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_4_F000
import Mathlib.Tactic

open Set

/-- Given a sequence of sets E_i,
   A sample ω belongs to liminf E_i iff ω occurs in E_i for all but finitely many indices i
-/
theorem thm_2_1_part1 {Ω : Type*} (E : ℕ → Set Ω) :
   (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) := by
  sorry
