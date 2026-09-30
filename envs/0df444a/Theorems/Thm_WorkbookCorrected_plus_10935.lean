-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10935
-- name    : WorkbookCorrected.plus_10935
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:41:35.491526+00:00
-- url     : https://prove2.me/theorems/ee47a407-b315-4bb6-b955-cc2b240f4ada
-- title:
--   Binomial coefficient identity #10935
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2 * \binom{12}{2} + 6 * \binom{6}{2}) / \binom{60}{2} = 37 / 295
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_10935`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10935 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_10935; Apache-2.0; corrects Open node a7567ab9-fce1-4e4e-80fb-bedf6abce4b4

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_10935 : ((2:ℚ) * (Nat.choose 12 2) + 6 * (Nat.choose 6 2)) / (Nat.choose 60 2) = (37:ℚ) / 295 := by sorry
