-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8153
-- name    : WorkbookCorrected.plus_8153
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:22.162843+00:00
-- url     : https://prove2.me/theorems/5a53bc36-ab04-44db-9cab-0b9bc2e99d6f
-- title:
--   Elementary arithmetic identity #8153
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10 * 5 * 5 = 250
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_8153`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8153 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8153; Apache-2.0; corrects Open node d133a91f-ab9e-45a6-b1c1-7b78f9a49a46

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_8153 : 10 * 5 * 5 = 250 := by sorry
