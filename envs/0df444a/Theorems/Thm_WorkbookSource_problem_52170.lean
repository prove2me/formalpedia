-- Prove2me | Theorems.Thm_WorkbookSource_problem_52170
-- name    : WorkbookSource.problem_52170
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:10:56.097736+00:00
-- url     : https://prove2.me/theorems/0225ef53-20fe-485b-abdb-093924df2a0b
-- title:
--   A normalized pairwise-product bound
-- statement:
--   prove that $ \frac {3(ab + bc + ca)}{(a + b + c)^2}\leq 1$ where $a, b, c$ are positive numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52170` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52170; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_52170 (a b c : ℝ) : 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≤ 1  :=  by sorry
