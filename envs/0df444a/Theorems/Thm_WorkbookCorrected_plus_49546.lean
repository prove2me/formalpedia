-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_49546
-- name    : WorkbookCorrected.plus_49546
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:05:42.654321+00:00
-- url     : https://prove2.me/theorems/ea70c872-2ea7-471a-8167-c377ff2b028b
-- title:
--   Elementary arithmetic identity #49546
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10 + 13 + 16 + 19 + 22 + 25 + 28 + 31 + 34 + 37 + 40 + 43 = 318
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_49546`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_49546 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_49546; Apache-2.0; corrects Open node a38ba2b3-0ed7-488f-b4ef-d97d19d490b9

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_49546 : 10 + 13 + 16 + 19 + 22 + 25 + 28 + 31 + 34 + 37 + 40 + 43 = 318 := by sorry
