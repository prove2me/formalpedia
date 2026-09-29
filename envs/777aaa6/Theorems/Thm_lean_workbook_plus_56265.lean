-- Prove2me | Theorems.Thm_lean_workbook_plus_56265
-- name    : lean_workbook_plus_56265
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/815f333f-a402-48b0-a2d6-190398f56f8a
-- statement:
--   Let $a=1+x,b=1+y,c=1+z,x,y,z\ge -1$ .Then $a^2+b^2+c^2+2abc+3-(1+a)(1+b)(1+c)=x^2+y^2+z^2+xyz.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56265 (a b c x y z : ℝ) (ha : a = 1 + x) (hb : b = 1 + y) (hc : c = 1 + z) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) : a^2 + b^2 + c^2 + 2 * a * b * c + 3 - (1 + a) * (1 + b) * (1 + c) = x^2 + y^2 + z^2 + x * y * z   :=  by sorry
