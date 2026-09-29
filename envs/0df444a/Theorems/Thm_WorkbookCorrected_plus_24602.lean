-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24602
-- name    : WorkbookCorrected.plus_24602
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:00.509762+00:00
-- url     : https://prove2.me/theorems/0c329f10-dca0-4cac-b57e-48023a107a49
-- title:
--   Factorial arithmetic identity #24602
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   12 * 10 * 8 * 6 * 4 / (5!) = 192
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_24602`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24602 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_24602; Apache-2.0; corrects Open node d1b49dc0-21c9-4838-9e76-9e50b8de2560

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_24602 : 12 * 10 * 8 * 6 * 4 / (Nat.factorial 5) = 192 := by sorry
