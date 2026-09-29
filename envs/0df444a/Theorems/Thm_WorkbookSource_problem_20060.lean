-- Prove2me | Theorems.Thm_WorkbookSource_problem_20060
-- name    : WorkbookSource.problem_20060
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:34.852209+00:00
-- url     : https://prove2.me/theorems/867d2632-2d1a-4797-922b-aacfae41338e
-- title:
--   A strict product bound on the unit circle
-- statement:
--   Let $a,b$ be reals such that $a^2+ b^ 2= 1.$ Prove that $(a+1)(b +2)<5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20060` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20060; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_20060 (a b: ℝ) (hab : a^2 + b^2 = 1): (a + 1) * (b + 2) < 5  :=  by sorry
