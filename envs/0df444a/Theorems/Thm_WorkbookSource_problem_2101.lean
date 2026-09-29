-- Prove2me | Theorems.Thm_WorkbookSource_problem_2101
-- name    : WorkbookSource.problem_2101
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:19.895061+00:00
-- url     : https://prove2.me/theorems/8d8ba54e-e5ed-45cd-871d-10da57e3b9b9
-- title:
--   A quadratic bound from a cubic inequality
-- statement:
--   If $x,y>0$ and $x^3+y^3\le x-y$, then $x^2+y^2\le1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2101` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2101; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_2101 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x - y) : x^2 + y^2 ≤ 1  :=  by sorry
