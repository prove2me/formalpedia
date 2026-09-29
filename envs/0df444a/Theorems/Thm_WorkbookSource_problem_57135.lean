-- Prove2me | Theorems.Thm_WorkbookSource_problem_57135
-- name    : WorkbookSource.problem_57135
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:02.569423+00:00
-- url     : https://prove2.me/theorems/86d55a02-9be9-49fc-9f90-6984e37340d2
-- title:
--   A pair-product bound from a rational inequality
-- statement:
--   From the inequality $\frac{(a+b+c)^2}{a^2+b^2+c^2+3} \leq 1$, deduce that $ab+bc+ca \leq \frac{3}{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57135` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57135; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_57135 (a b c : ℝ) : (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2  :=  by sorry
