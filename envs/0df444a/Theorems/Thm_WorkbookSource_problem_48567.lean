-- Prove2me | Theorems.Thm_WorkbookSource_problem_48567
-- name    : WorkbookSource.problem_48567
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:32.231224+00:00
-- url     : https://prove2.me/theorems/ba77fdd8-e2a1-46a1-ab79-0f23693a9c95
-- title:
--   A sum of three fractions with a common denominator
-- statement:
--   Correction: The inequality holds only for positive $a, b, c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48567` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48567; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_48567 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + c + a) + b / (c + a + b) + c / (a + b + c) < 3 / 2  :=  by sorry
