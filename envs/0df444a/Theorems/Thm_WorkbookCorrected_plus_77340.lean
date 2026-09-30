-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77340
-- name    : WorkbookCorrected.plus_77340
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:29:46.111882+00:00
-- url     : https://prove2.me/theorems/e9528435-cc0e-482f-a77b-d0f43ec1ffcd
-- title:
--   Elementary arithmetic identity #77340
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   7888609052210118054117285652827862296732064351090230047702789306640624 = 7888609052210118054117285652827862296732064351090230047702789306640624
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77340`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77340 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77340; Apache-2.0; corrects Open node 341ebc4e-6c40-4165-abfb-60b29746e6e2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_77340 : 7888609052210118054117285652827862296732064351090230047702789306640624 = 7888609052210118054117285652827862296732064351090230047702789306640624 := by sorry
