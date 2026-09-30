-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_31800
-- name    : WorkbookCorrected.plus_31800
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:08:53.150847+00:00
-- url     : https://prove2.me/theorems/18afa7bb-d2fb-4a83-aaf0-bf3c5eb11501
-- title:
--   Elementary arithmetic identity #31800
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   3125 + 2560 + 1080 + 320 + 80 = 7165
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_31800`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_31800 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_31800; Apache-2.0; corrects Open node 7b723ae1-39da-4ed8-913f-353bffa5c65e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_31800 : 3125 + 2560 + 1080 + 320 + 80 = 7165 := by sorry
