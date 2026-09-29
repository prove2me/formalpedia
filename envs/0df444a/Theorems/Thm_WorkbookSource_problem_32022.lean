-- Prove2me | Theorems.Thm_WorkbookSource_problem_32022
-- name    : WorkbookSource.problem_32022
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:52.579119+00:00
-- url     : https://prove2.me/theorems/a2810ed9-a32e-4079-9390-fa76b687bc83
-- title:
--   A cubic consequence of a rational constraint
-- statement:
--   Let $a,b,c$ be positive real numbers such that $\frac{a}{b+c}+\frac{b}{c+a}=\frac{7}{3}. $ Prove that
--    $$a^3+b^3+c^3\geq 5abc$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32022` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32022; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_32022 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) = 7 / 3 → a ^ 3 + b ^ 3 + c ^ 3 >= 5 * a * b * c)  :=  by sorry
