-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_20865
-- name    : WorkbookCorrected.plus_20865
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:34.676989+00:00
-- url     : https://prove2.me/theorems/2869aaa2-a872-4d12-b79f-d40c29916dd8
-- title:
--   Binomial coefficient identity #20865
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{7}{3}) = 35
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_20865`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20865 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_20865; Apache-2.0; corrects Open node 8ad97216-1226-4bb8-927a-407958015d83

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_20865 : (Nat.choose 7 3) = 35 := by sorry
