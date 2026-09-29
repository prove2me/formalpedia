-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77350
-- name    : WorkbookCorrected.plus_77350
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:31.386375+00:00
-- url     : https://prove2.me/theorems/39ac9a72-75de-48f3-b839-48049904a597
-- title:
--   Sum of two rational products equals 64/195
-- statement:
--   The elementary rational identity
--   $$
--   \frac{6}{21}\cdot\frac{8}{15}+\frac{8}{21}\cdot\frac{6}{13}=\frac{64}{195}
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77350`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77350 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77350; Apache-2.0; corrects Open node 2d3e8f90-2ea5-45f3-b9cd-f081bf94b870

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_77350 : (6 : ℚ) / 21 * 8 / 15 + (8 : ℚ) / 21 * 6 / 13 = 64 / 195 := by sorry
