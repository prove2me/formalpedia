-- Prove2me | Theorems.Thm_WorkbookSource_problem_49227
-- name    : WorkbookSource.problem_49227
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:37.041105+00:00
-- url     : https://prove2.me/theorems/bc28f7d7-351e-40d9-9e5a-a038421e53b5
-- title:
--   A mixed polynomial bound on a simplex
-- statement:
--   Let $a, b, c\geq 0$ and $a+b+c=3$ . Then $$3a^2+3b^2+c^3\leq 27$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49227` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49227; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_49227 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3) : 3 * a ^ 2 + 3 * b ^ 2 + c ^ 3 ≤ 27  :=  by sorry
