-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_54661
-- name    : WorkbookCorrected.plus_54661
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:22:12.840987+00:00
-- url     : https://prove2.me/theorems/6caa35c8-462e-4da8-967b-4675cdaceaa9
-- title:
--   Elementary arithmetic identity #54661
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   123 + 4 + 5 + 6 + 7 + 8 - 9 = 144 ∧ 123 - 4 - 5 + 6 + 7 + 8 + 9 = 144
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_54661`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_54661 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_54661; Apache-2.0; corrects Open node b9501ede-dd46-485f-b52c-3a8560bb2e1e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_54661 : (123 + 4 + 5 + 6 + 7 + 8 - 9 = 144) ∧ (123 - 4 - 5 + 6 + 7 + 8 + 9 = 144) := by sorry
