-- Prove2me | Theorems.Thm_WorkbookSource_problem_9978
-- name    : WorkbookSource.problem_9978
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:32.619447+00:00
-- url     : https://prove2.me/theorems/32808067-2f0f-4ad3-9890-0bdbdd4a55b2
-- title:
--   A quadratic symmetric value from a difference of cubes
-- statement:
--   Find the value of $a^2+ab+b^2$ given $a^3-b^3=24$ and $a-b=2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9978` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9978; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9978 (a b : ℝ) (h₁ : a^3 - b^3 = 24) (h₂ : a - b = 2) : a^2 + a * b + b^2 = 12  :=  by sorry
