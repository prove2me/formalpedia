-- Prove2me | Theorems.Thm_WorkbookSource_problem_32941
-- name    : WorkbookSource.problem_32941
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:10.73344+00:00
-- url     : https://prove2.me/theorems/c9f079ab-af00-4e57-bcfc-a5bfc6dfb598
-- title:
--   A quadratic bound with a pairwise-product constraint
-- statement:
--   Let $ a,$ $ b$ and $ c$ are non-negative numbers such that $ ab+ac+bc=3.$ Prove that
--    $ a^2+b^2+c^2+15\geq6(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32941` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32941; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32941 (a b c : ℝ) (habc : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 15 ≥ 6 * (a + b + c)  :=  by sorry
