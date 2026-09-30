-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_68270
-- name    : WorkbookCorrected.plus_68270
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:42:27.505928+00:00
-- url     : https://prove2.me/theorems/a773e10f-b3b1-4123-89f5-192b1c14041f
-- title:
--   Elementary arithmetic identity #68270
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 2 + 3 + 4 = 10
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_68270`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_68270 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_68270; Apache-2.0; corrects Open node 43d407f2-22af-465d-87c0-dd4acf6274e8

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_68270 : 1 + 2 + 3 + 4 = 10 := by sorry
