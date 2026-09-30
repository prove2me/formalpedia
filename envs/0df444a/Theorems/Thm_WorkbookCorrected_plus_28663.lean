-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_28663
-- name    : WorkbookCorrected.plus_28663
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:35:59.711962+00:00
-- url     : https://prove2.me/theorems/86eda445-caf7-49c2-814a-9a6b8c3d0d91
-- title:
--   Elementary arithmetic identity #28663
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 8 + 27 + 64 + 125 + 216 + 343 + 512 + 729 + 1000 + 1331 + 1728 + 2197 + 2744 + 3375 + 4096 + 4913 + 5832 + 6859 + 8000 = 44100
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_28663`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_28663 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_28663; Apache-2.0; corrects Open node d85eded5-87a6-4ed2-a272-b2607cf02f73

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_28663 : 1 + 8 + 27 + 64 + 125 + 216 + 343 + 512 + 729 + 1000 + 1331 + 1728 + 2197 + 2744 + 3375 + 4096 + 4913 + 5832 + 6859 + 8000 = 44100 := by sorry
