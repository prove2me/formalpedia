-- Prove2me | Theorems.Thm_lean_workbook_plus_30972
-- name    : lean_workbook_plus_30972
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b0f1fa8e-75a7-4ad2-a5ac-185284be3a4f
-- statement:
--   Prove that the equation $y^2-x^3=1$ has only two integer solutions, which are $x=2,y=3$ or $x=2,y=-3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30972 : { (x,y) : ℤ × ℤ | y^2 - x^3 = 1}  =  {(2,3), (2,-3)}   :=  by sorry
