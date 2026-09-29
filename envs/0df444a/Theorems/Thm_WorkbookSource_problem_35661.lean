-- Prove2me | Theorems.Thm_WorkbookSource_problem_35661
-- name    : WorkbookSource.problem_35661
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:55.363521+00:00
-- url     : https://prove2.me/theorems/bcf20335-7935-4a39-842e-4be72585918f
-- title:
--   A product divided by its consecutive sum
-- statement:
--   The quotient of the product of the first eight positive integers by their sum is
--
--   $$\frac{1\cdot2\cdot3\cdot4\cdot5\cdot6\cdot7\cdot8}{1+2+3+4+5+6+7+8}=1120.$$
--
--   The numerator is divisible by the denominator, so the source natural-number quotient agrees with ordinary division.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35661` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35661; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35661 (h : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 ≠ 0) : 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 / (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8) = 1120  :=  by sorry
