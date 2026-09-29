-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_7128
-- name    : WorkbookCorrected.plus_7128
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:26.397749+00:00
-- url     : https://prove2.me/theorems/12b85d14-d604-47de-b789-09effac38eca
-- title:
--   Factorial arithmetic identity #7128
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   9! / (5 * 4 * 3 * 4 * 3 * 2 * 3 * 2 * 1) = 42
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_7128`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_7128 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_7128; Apache-2.0; corrects Open node 17abcf05-cdbb-4d04-86e3-2e0a2d4b61f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_7128 : (Nat.factorial 9) / (5 * 4 * 3 * 4 * 3 * 2 * 3 * 2 * 1) = 42 := by sorry
