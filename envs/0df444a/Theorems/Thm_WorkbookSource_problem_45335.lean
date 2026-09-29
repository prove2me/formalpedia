-- Prove2me | Theorems.Thm_WorkbookSource_problem_45335
-- name    : WorkbookSource.problem_45335
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:19.79671+00:00
-- url     : https://prove2.me/theorems/87e28369-8b13-42e5-8f3d-25142db5c4ac
-- title:
--   A quartic with no real roots
-- statement:
--   Prove that $4x^{4} -2x+c=0$ has no real roots if $c > \frac{3}{4}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45335` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45335; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_45335 (c : ℝ) (h : c > 3/4) : ¬ (∃ x, 4*x^4 - 2*x + c = 0)  :=  by sorry
