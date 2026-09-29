-- Prove2me | Theorems.Thm_WorkbookSource_problem_40553
-- name    : WorkbookSource.problem_40553
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:09.959559+00:00
-- url     : https://prove2.me/theorems/642d317f-8181-4abd-bd0f-4b5686e53e06
-- title:
--   An absolute difference by cases
-- statement:
--   For real numbers $x,y$,
--
--   $$|x-y|=\begin{cases}x-y&x>y,\\y-x&x\le y.\end{cases}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40553` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40553; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40553 (x y : ℝ) : |x - y| = if x > y then x - y else y - x  :=  by sorry
