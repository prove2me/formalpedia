-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_67208
-- name    : WorkbookCorrected.plus_67208
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:17:52.68955+00:00
-- url     : https://prove2.me/theorems/13b7e49c-4a1c-4111-bc6e-2d5ef08414ac
-- title:
--   Binomial coefficient identity #67208
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{14}{2})^2 = 8281
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_67208`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_67208 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_67208; Apache-2.0; corrects Open node 76b63b10-46d9-4147-a943-92d309750a1c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_67208 : (Nat.choose 14 2) ^ 2 = 8281 := by sorry
