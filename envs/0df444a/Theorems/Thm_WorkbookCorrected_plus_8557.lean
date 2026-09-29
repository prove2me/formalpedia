-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8557
-- name    : WorkbookCorrected.plus_8557
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:38.547189+00:00
-- url     : https://prove2.me/theorems/357460ae-0df3-422a-afb9-85bf86dbeca9
-- title:
--   Elementary arithmetic identity #8557
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   233 - 23 - 14 + 4 = 200
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_8557`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8557 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8557; Apache-2.0; corrects Open node 33283d11-4c99-43a0-b2a8-55e541968a06

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_8557 : 233 - 23 - 14 + 4 = 200 := by sorry
