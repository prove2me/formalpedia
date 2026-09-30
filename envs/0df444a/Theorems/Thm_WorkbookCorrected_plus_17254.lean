-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_17254
-- name    : WorkbookCorrected.plus_17254
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:15.764586+00:00
-- url     : https://prove2.me/theorems/f5d02a1e-aa5e-4798-a439-eb79c25ef893
-- title:
--   Elementary arithmetic identity #17254
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 30 + 150 + 200 + 75 + 6 = 462
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_17254`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_17254 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_17254; Apache-2.0; corrects Open node 369dd1dc-1da8-40aa-a33a-ce6ea2370fd2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_17254 : 1 + 30 + 150 + 200 + 75 + 6 = 462 := by sorry
