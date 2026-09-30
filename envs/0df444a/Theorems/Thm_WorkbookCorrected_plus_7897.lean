-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_7897
-- name    : WorkbookCorrected.plus_7897
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:01:42.599095+00:00
-- url     : https://prove2.me/theorems/43a7e5e6-aed5-4b39-86f4-b37485117daf
-- title:
--   Elementary arithmetic identity #7897
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 2 + 3 + 4 = 10
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_7897`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_7897 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_7897; Apache-2.0; corrects Open node 6f447709-27cc-4c0d-9e75-7fa497c09c55

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_7897 : 1 + 2 + 3 + 4 = 10 := by sorry
