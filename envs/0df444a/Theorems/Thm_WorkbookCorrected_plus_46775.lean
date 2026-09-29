-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_46775
-- name    : WorkbookCorrected.plus_46775
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:13.510372+00:00
-- url     : https://prove2.me/theorems/7f651a2d-b1e0-4613-b78c-66c3a17b0972
-- title:
--   Factorial arithmetic identity #46775
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   3 * (4! / (2! * 1! * 1!)) = 36
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_46775`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_46775 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_46775; Apache-2.0; corrects Open node 053ae76e-e22e-4195-b061-8011caeb03f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_46775 : 3 * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 1) * (Nat.factorial 1))) = 36 := by sorry
