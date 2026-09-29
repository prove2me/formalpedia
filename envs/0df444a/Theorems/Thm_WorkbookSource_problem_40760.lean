-- Prove2me | Theorems.Thm_WorkbookSource_problem_40760
-- name    : WorkbookSource.problem_40760
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:18.985728+00:00
-- url     : https://prove2.me/theorems/11f89522-c739-4578-851f-9ed8e4f2868d
-- title:
--   A weighted sum of three real squares
-- statement:
--   For real $x,y$,
--
--   $$3\left(x+\frac23\right)^2+6\left(y+\frac13\right)^2+(x-2y)^2\ge0.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40760` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40760; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40760 (x y : ℝ) : (3 * (x + 2 / 3) ^ 2 + 6 * (y + 1 / 3) ^ 2 + (x - 2 * y) ^ 2) ≥ 0  :=  by sorry
