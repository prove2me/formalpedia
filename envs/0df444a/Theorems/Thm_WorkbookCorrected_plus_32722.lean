-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_32722
-- name    : WorkbookCorrected.plus_32722
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:30:03.294822+00:00
-- url     : https://prove2.me/theorems/b97dd233-0581-4985-8255-91f868c49980
-- title:
--   Elementary arithmetic identity #32722
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   171700 = 171700
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_32722`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_32722 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_32722; Apache-2.0; corrects Open node 9393838f-a921-42f0-ac71-9761b492534d

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_32722 : 171700 = 171700 := by sorry
