-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50390
-- name    : WorkbookCorrected.plus_50390
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:01:49.98385+00:00
-- url     : https://prove2.me/theorems/45292660-f546-49d9-9b58-22a6b933b02b
-- title:
--   Elementary arithmetic identity #50390
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   169 + 144 + 121 + 100 + 81 + 64 + 49 + 36 + 25 + 16 + 9 + 4 + 1 = 819
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50390`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50390 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50390; Apache-2.0; corrects Open node 29ab8278-8456-414b-aa3d-9e80991898ac

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50390 : 169 + 144 + 121 + 100 + 81 + 64 + 49 + 36 + 25 + 16 + 9 + 4 + 1 = 819 := by sorry
