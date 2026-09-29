-- Prove2me | Theorems.Thm_WorkbookSource_problem_52646
-- name    : WorkbookSource.problem_52646
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:41.325052+00:00
-- url     : https://prove2.me/theorems/97b7cc85-7145-4bc6-9068-d807bd20e7b3
-- title:
--   A bound with a fixed sum
-- statement:
--   Let $x,y\geq 1 $ and $x+y= 3.$ Prove that $(y^2 + y+ 1)(x + 1) + (x^2-x- 1)(y- 1) \ge 9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52646` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52646; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_52646 (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x + y = 3) : (y^2 + y + 1) * (x + 1) + (x^2 - x - 1) * (y - 1) ≥ 9  :=  by sorry
