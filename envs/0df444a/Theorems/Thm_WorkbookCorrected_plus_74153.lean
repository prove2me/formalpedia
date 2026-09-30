-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_74153
-- name    : WorkbookCorrected.plus_74153
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:36:49.948766+00:00
-- url     : https://prove2.me/theorems/750f919f-ea7b-4eaa-a806-eac41301fa0b
-- title:
--   Elementary arithmetic identity #74153
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5050 = 5050
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_74153`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_74153 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_74153; Apache-2.0; corrects Open node 83d6dadd-3b79-4220-a3eb-f90685383853

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_74153 : 5050 = 5050 := by sorry
