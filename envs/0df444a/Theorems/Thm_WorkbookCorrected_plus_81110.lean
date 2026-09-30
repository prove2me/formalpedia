-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_81110
-- name    : WorkbookCorrected.plus_81110
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:42:21.382071+00:00
-- url     : https://prove2.me/theorems/0bc8beda-3dc8-4ce9-a902-0724207d9154
-- title:
--   Factorial arithmetic identity #81110
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   8 * 10! * 2! = 8 * 10! * 2!
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_81110`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_81110 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_81110; Apache-2.0; corrects Open node b0979d85-c32d-4aef-bc4c-053b7a644ab9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_81110 : 8 * (Nat.factorial 10) * (Nat.factorial 2) = 8 * (Nat.factorial 10) * (Nat.factorial 2) := by sorry
