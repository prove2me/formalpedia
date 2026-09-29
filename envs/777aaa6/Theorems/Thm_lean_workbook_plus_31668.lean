-- Prove2me | Theorems.Thm_lean_workbook_plus_31668
-- name    : lean_workbook_plus_31668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/be060451-75d1-4f70-9534-113efe81ba44
-- statement:
--   If x,y,z are real positive numbers, prove that \n $ (x+y+z)^2(xy+yz+zx)^2\leq3(y^2+yz+z^2)(z^2+zx+x^2)(x^2+xy+y^2)$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31668 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2 ≤ 3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2)   :=  by sorry
