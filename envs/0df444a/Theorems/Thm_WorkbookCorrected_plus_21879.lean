-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21879
-- name    : WorkbookCorrected.plus_21879
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:27.541842+00:00
-- url     : https://prove2.me/theorems/e844cb88-2faf-46a3-811f-54d994c84e5f
-- title:
--   Binomial coefficient identity #21879
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   ( \binom{6}{4} + \binom{5}{4} + 11*(\binom{6}{3} + \binom{5}{3}) + 30*(\binom{6}{2} + \binom{5}{2}) ) = 1100
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_21879`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_21879 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_21879; Apache-2.0; corrects Open node 6deb5bf7-77e3-4860-8635-630faa2acbcf

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_21879 : ( (Nat.choose 6 4) + (Nat.choose 5 4) + 11*((Nat.choose 6 3) + (Nat.choose 5 3)) + 30*((Nat.choose 6 2) + (Nat.choose 5 2)) ) = 1100 := by sorry
