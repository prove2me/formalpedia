-- Prove2me | Theorems.Thm_WorkbookSource_problem_20256
-- name    : WorkbookSource.problem_20256
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:32.973824+00:00
-- url     : https://prove2.me/theorems/7bbb4678-e0e6-4a32-972f-21ba6db08075
-- title:
--   A mixed quadratic and cubic bound
-- statement:
--   Let $a, b, c\geq 0$ and $a+b+c=3$ .Then $$3a^2+3b^2+c^3\leq 27$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20256` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20256; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_20256 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3) : 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27  :=  by sorry
