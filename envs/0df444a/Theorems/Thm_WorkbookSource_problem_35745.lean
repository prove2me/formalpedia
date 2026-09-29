-- Prove2me | Theorems.Thm_WorkbookSource_problem_35745
-- name    : WorkbookSource.problem_35745
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:05.638676+00:00
-- url     : https://prove2.me/theorems/9775517f-57a7-488a-97a3-428531ec40e0
-- title:
--   An inequality for the sine of a sum
-- statement:
--   Prove that $(\sin(x+y))^2 \ge \sin(2x) \cdot \sin(2y)$ for all $x, y$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35745` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35745; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_35745 (x y : ℝ) : (sin (x + y))^2 ≥ sin (2*x) * sin (2*y)  :=  by sorry
