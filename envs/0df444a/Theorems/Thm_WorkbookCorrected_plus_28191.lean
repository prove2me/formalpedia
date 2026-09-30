-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_28191
-- name    : WorkbookCorrected.plus_28191
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:14.891828+00:00
-- url     : https://prove2.me/theorems/207e36bf-1a1b-40eb-9084-d930505aa46e
-- title:
--   Elementary arithmetic identity #28191
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 6 + 15 + 20 + 15 + 6 + 1 = 64
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_28191`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_28191 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_28191; Apache-2.0; corrects Open node 61d342d2-ed2a-49c9-b5da-1c7097420916

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_28191 : 1 + 6 + 15 + 20 + 15 + 6 + 1 = 64 := by sorry
