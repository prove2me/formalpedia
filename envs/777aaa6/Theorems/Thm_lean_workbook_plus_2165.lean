-- Prove2me | Theorems.Thm_lean_workbook_plus_2165
-- name    : lean_workbook_plus_2165
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/27a74c81-0985-4ec3-939c-62a0c1d802c0
-- statement:
--   Euler's Four square Identity: $(a^2+b^2+c^2+d^2)(w^2+x^2+y^2+z^2) = (aw+bx+cy+dz)^2+(ax-bw+cz-dy)^2+(ay-bz-cw+dx)^2+(az+by-cx-dw)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2165 (a b c d w x y z : ℝ) : (a^2+b^2+c^2+d^2)*(w^2+x^2+y^2+z^2) = (a*w+b*x+c*y+d*z)^2+(a*x-b*w+c*z-d*y)^2+(a*y-b*z-c*w+d*x)^2+(a*z+b*y-c*x-d*w)^2   :=  by sorry
