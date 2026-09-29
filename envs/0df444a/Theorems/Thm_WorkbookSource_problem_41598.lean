-- Prove2me | Theorems.Thm_WorkbookSource_problem_41598
-- name    : WorkbookSource.problem_41598
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:32.182952+00:00
-- url     : https://prove2.me/theorems/fd1ea1d1-f090-44ac-b2d5-cf1ca7cc765c
-- title:
--   Completing a square in a sine expression
-- statement:
--   For every real $x$,
--
--   $$2(1-2\sin^2x)+2\sin x=\frac94-4\left(\sin x-\frac14\right)^2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41598` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41598; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_41598 (x : ℝ) : 2 * (1 - 2 * Real.sin x ^ 2) + 2 * Real.sin x = 9 / 4 - 4 * (Real.sin x - 1 / 4) ^ 2  :=  by sorry
