-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_52050
-- name    : WorkbookCorrected.plus_52050
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:30:28.278666+00:00
-- url     : https://prove2.me/theorems/c7fa7aed-9709-4b2a-82fb-46161e057387
-- title:
--   Elementary arithmetic identity #52050
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 25 + 300 + 2300 + 12650 + 53130 + 177100 + 480700 + 1081575 + 2042975 + 3268760 + 4457400 + 5200300 + 5200300 + 4457400 + 3268760 + 2042975 + 1081575 + 480700 + 177100 + 53130 + 12650 + 2300 + 300 + 25 + 1 = 2^25
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_52050`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_52050 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_52050; Apache-2.0; corrects Open node 9e1bf98e-9dfd-4168-ad65-b4885ab1f8f2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_52050 : 1 + 25 + 300 + 2300 + 12650 + 53130 + 177100 + 480700 + 1081575 + 2042975 + 3268760 + 4457400 + 5200300 + 5200300 + 4457400 + 3268760 + 2042975 + 1081575 + 480700 + 177100 + 53130 + 12650 + 2300 + 300 + 25 + 1 = 2 ^ 25 := by sorry
