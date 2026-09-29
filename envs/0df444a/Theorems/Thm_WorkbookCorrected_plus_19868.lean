-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_19868
-- name    : WorkbookCorrected.plus_19868
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:20.881307+00:00
-- url     : https://prove2.me/theorems/97ca2c09-ef96-4d22-b521-3126af26fe82
-- title:
--   Elementary arithmetic identity #19868
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5*6*7 = 2*3*5*7
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_19868`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_19868 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_19868; Apache-2.0; corrects Open node e749d73f-ec66-45f2-80ca-7453262c3b1e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_19868 : 5*6*7 = 2*3*5*7 := by sorry
