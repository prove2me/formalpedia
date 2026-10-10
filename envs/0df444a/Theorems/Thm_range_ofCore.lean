-- Prove2me | Theorems.Thm_range_ofCore
-- name    : range_ofCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:56.84029+00:00
-- url     : https://prove2.me/theorems/0a5ab07c-c7b4-475b-a24f-c9c4b72b3df6
-- title:
--   `range_ofCore` : Set.range ofCore = FinSupport
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaFreeCompletion`.
--
--   `range_ofCore` : Set.range ofCore = FinSupport
--
--   Formalization note: Lean 4 identifier `range_ofCore`.

-- Generated from ChapterPaFreeCompletion.lean — theorem range_ofCore
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4
open BookProof.ChapterRieszFischer


open Set
open Filter
open BookProof.ChapterRieszFischer

theorem range_ofCore : Set.range ofCore = FinSupport := by sorry
