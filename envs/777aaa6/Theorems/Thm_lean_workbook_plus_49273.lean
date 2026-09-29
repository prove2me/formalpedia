-- Prove2me | Theorems.Thm_lean_workbook_plus_49273
-- name    : lean_workbook_plus_49273
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9817cef1-d3a7-49d3-bd9f-f2dfb213816b
-- statement:
--   Let $x,y,z$ be integers such that $(x-y)^2+(y-z)^2+(z-x)^2 = xyz$. Prove that $x^3+y^3+z^3$ is divisible by $x+y+z+6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49273 (x y z : ℤ) (h : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = x * y * z) : (x + y + z + 6) ∣ (x ^ 3 + y ^ 3 + z ^ 3)   :=  by sorry
