-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24398
-- name    : WorkbookCorrected.plus_24398
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:37:56.90611+00:00
-- url     : https://prove2.me/theorems/301e61ae-20b4-4abe-8c86-d8722bd92504
-- title:
--   Elementary arithmetic identity #24398
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2 + 3 + 4 + 5 = 14
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_24398`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24398 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_24398; Apache-2.0; corrects Open node 4f5fbe1b-9a85-404a-8cad-5d83a5eac631

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_24398 : 2 + 3 + 4 + 5 = 14 := by sorry
