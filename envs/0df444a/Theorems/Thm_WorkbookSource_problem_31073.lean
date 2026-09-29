-- Prove2me | Theorems.Thm_WorkbookSource_problem_31073
-- name    : WorkbookSource.problem_31073
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:47.490707+00:00
-- url     : https://prove2.me/theorems/8aa52428-7b0e-48af-ae9f-f1313bd9844c
-- title:
--   Solving an equation with a half
-- statement:
--   Solve for $n$ when $n+2 = \frac{n}{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31073` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31073; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_31073 (n : ℝ) : n + 2 = n / 2 ↔ n = -4  :=  by sorry
