-- Prove2me | Theorems.Thm_WorkbookSource_problem_8681
-- name    : WorkbookSource.problem_8681
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:19.505955+00:00
-- url     : https://prove2.me/theorems/351a2e35-7474-4735-b071-05e02c4aacf7
-- title:
--   The first two terms of a rational geometric series
-- statement:
--   Calculate the sum of the first two terms of the geometric series with $a = 2$ and $r = \frac{1}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8681` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8681; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_8681 (a r n : ℝ) (ha : a = 2) (hr : r = 1/3) (hn : n = 2) : a + a*r = 8/3  :=  by sorry
