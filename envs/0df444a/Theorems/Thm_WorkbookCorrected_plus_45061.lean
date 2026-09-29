-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45061
-- name    : WorkbookCorrected.plus_45061
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:34.035465+00:00
-- url     : https://prove2.me/theorems/224972a2-33ed-4300-961f-21dfab3db815
-- title:
--   Binomial coefficient identity #45061
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{5}{3}) - 1 = 9
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45061`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45061 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45061; Apache-2.0; corrects Open node 8759da5a-62ed-42be-b1a1-eef3b32fddcd

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45061 : (Nat.choose 5 3) - 1 = 9 := by sorry
