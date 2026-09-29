-- Prove2me | Theorems.Thm_WorkbookSource_problem_12605
-- name    : WorkbookSource.problem_12605
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:17.168111+00:00
-- url     : https://prove2.me/theorems/76be93d9-d3d9-4c11-a8a7-aa24f579b9ef
-- title:
--   A bound for three variables with a cubic constraint
-- statement:
--   If real $a,b,c$ satisfy $a^3+b^3+c^3-1=3(a-1)(b-1)(c-1)$, then $a+b+c\le2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12605` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12605; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_12605 (a b c : ℝ) (ha : a^3 + b^3 + c^3 - 1 = 3 * (a - 1) * (b - 1) * (c - 1)) : a + b + c ≤ 2  :=  by sorry
