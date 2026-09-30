-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_246
-- name    : WorkbookCorrected.plus_246
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T10:41:14.08729+00:00
-- url     : https://prove2.me/theorems/a2095868-cd5a-4c86-be56-acd24ee12109
-- title:
--   Binomial coefficient identity #246
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (Nat.choose (4+218-1) 218) = 1774630
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_246`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_246 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_246; Apache-2.0; corrects Open node 0e92b179-2070-472c-a0e4-22030b4535eb

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_246 : (Nat.choose (4+218-1) 218) = 1774630 := by sorry
