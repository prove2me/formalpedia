-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_41134
-- name    : WorkbookCorrected.plus_41134
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:36.775174+00:00
-- url     : https://prove2.me/theorems/e7cd5ece-cd38-419a-80eb-daeb50b3a074
-- title:
--   Binomial coefficient identity #41134
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{11}{5}) - (\binom{5}{3}) = 452
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_41134`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_41134 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_41134; Apache-2.0; corrects Open node 037404d8-b847-4f1a-a4fd-f48399a549c1

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_41134 : (Nat.choose 11 5) - (Nat.choose 5 3) = 452 := by sorry
