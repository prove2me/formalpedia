-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_59225
-- name    : WorkbookCorrected.plus_59225
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:38.824885+00:00
-- url     : https://prove2.me/theorems/51c67e01-cff5-45ff-9c10-d10c312a5a60
-- title:
--   Binomial coefficient identity #59225
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{9}{3} * \binom{6}{3} * \binom{3}{3}) = 1680
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_59225`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_59225 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_59225; Apache-2.0; corrects Open node 6ddcd42e-60b5-429b-b26a-2daa067c1d79

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_59225 : ((Nat.choose 9 3) * (Nat.choose 6 3) * (Nat.choose 3 3)) = 1680 := by sorry
