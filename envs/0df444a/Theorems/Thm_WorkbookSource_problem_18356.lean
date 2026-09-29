-- Prove2me | Theorems.Thm_WorkbookSource_problem_18356
-- name    : WorkbookSource.problem_18356
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:56.138456+00:00
-- url     : https://prove2.me/theorems/889ecf0c-c41d-4175-9295-736bfd6eec70
-- title:
--   A quadratic has no real roots
-- statement:
--   The equation $x^2 - x + 1 = 0$ has no real solutions.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18356` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18356; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18356 : ¬∃ x : ℝ, x^2 - x + 1 = 0  :=  by sorry
