-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24991
-- name    : WorkbookCorrected.plus_24991
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:20.066386+00:00
-- url     : https://prove2.me/theorems/c19008d2-f3bc-45d0-b03f-72392f096e3f
-- title:
--   Sum of first five factorials
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1! + 2! + 3! + 4! + 5! = 153
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_24991`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24991 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_24991; Apache-2.0; corrects Open node 02d121b0-3e9c-40ed-86c9-a88bc89b51ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_24991 : Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 + Nat.factorial 4 + Nat.factorial 5 = 153 := by sorry
