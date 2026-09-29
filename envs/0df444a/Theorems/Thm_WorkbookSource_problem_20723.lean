-- Prove2me | Theorems.Thm_WorkbookSource_problem_20723
-- name    : WorkbookSource.problem_20723
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:16.823511+00:00
-- url     : https://prove2.me/theorems/226cf84b-471e-4f1e-ac32-b211103790f1
-- title:
--   A fifth-power identity under a linear constraint
-- statement:
--   If \\(x+y+1=0\\) then \\(2(x^5+y^5+1)=5xy(x^2+y^2+1)\\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20723` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20723; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20723 (x y : ℝ) (h : x + y + 1 = 0) :
  2 * (x^5 + y^5 + 1) = 5 * x * y * (x^2 + y^2 + 1)  :=  by sorry
