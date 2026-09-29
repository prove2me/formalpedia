-- Prove2me | Theorems.Thm_WorkbookSource_problem_36034
-- name    : WorkbookSource.problem_36034
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:05.014839+00:00
-- url     : https://prove2.me/theorems/42e9aa9d-3e8a-449e-9a3b-5d1c7504fd7c
-- title:
--   A product bound on the unit sphere
-- statement:
--   Let $a,b,c,d \in \mathbb{R}$ such that $a^2 + b^2 + c^2 + d^2 = 1$ . Prove that $(1-a)(1-b) \ge cd$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36034` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36034; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_36034 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
  (1 - a) * (1 - b) ≥ c * d  :=  by sorry
