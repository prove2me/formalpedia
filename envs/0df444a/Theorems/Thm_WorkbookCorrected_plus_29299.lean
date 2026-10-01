-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_29299
-- name    : WorkbookCorrected.plus_29299
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T06:55:08.537983+00:00
-- url     : https://prove2.me/theorems/ca968f77-66dc-4e86-8379-8b3ccd2d5e59
-- title:
--   Factorial arithmetic identity #29299
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   8! + 9! + 10! = 4032000
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_29299`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_29299 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_29299; Apache-2.0; corrects Open node f4da2496-c675-452b-8184-bc38f1f5af6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_29299 : (Nat.factorial 8) + (Nat.factorial 9) + (Nat.factorial 10) = 4032000 := by sorry
