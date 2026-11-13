-- Prove2me | Theorems.Thm_heine_borel
-- name    : heine_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:17:54.866828+00:00
-- url     : https://prove2.me/theorems/64b2c902-c661-4e09-8ad2-844fd8ceab8e
-- title:
--   ProbabilityTheory_chapter_03_thm_3_4_F000: heine_borel
-- statement:
--   Source theorem `heine_borel` extracted from `ProbabilityTheory.chapter_03.thm_3_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_4.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_4_F000
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded
open Set Metric Bornology

theorem heine_borel (A : Set ℝ) :
    IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), (∀ i, IsOpen (U i)) → (A ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) := by
  sorry
