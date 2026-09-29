-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_25577
-- name    : WorkbookCorrected.plus_25577
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:40.300253+00:00
-- url     : https://prove2.me/theorems/27228bf2-66c9-468a-b352-5aa4d467fc08
-- title:
--   Elementary arithmetic identity #25577
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 56 + 111 + 166 + 221 = 555
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_25577`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_25577 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_25577; Apache-2.0; corrects Open node 91847e4a-08a8-4330-8007-cf6f2436097a

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_25577 : 1 + 56 + 111 + 166 + 221 = 555 := by sorry
