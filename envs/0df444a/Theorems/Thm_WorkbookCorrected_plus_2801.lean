-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_2801
-- name    : WorkbookCorrected.plus_2801
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T04:21:56.607218+00:00
-- url     : https://prove2.me/theorems/2f58bb26-c6ce-4dc2-844e-ed6a8763e437
-- title:
--   Elementary inequality #2801
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{7}{2}) < 6 * (\binom{3}{2}) + 4 * (\binom{2}{2})
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_2801`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_2801 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_2801; Apache-2.0; corrects Open node 8fe52561-61c2-44c7-ae8d-c1a087af2ed9

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_2801 : (Nat.choose 7 2) < 6 * (Nat.choose 3 2) + 4 * (Nat.choose 2 2) := by sorry
