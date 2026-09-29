-- Prove2me | Theorems.Thm_lean_workbook_plus_73932
-- name    : lean_workbook_plus_73932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7de79739-7f00-46ad-965e-79b92534bd3f
-- statement:
--   Let $x,y,z$ be non-negative and $2(xy+yz+zx)\geq x^2+y^2+z^2$. Prove that $(5A)[\sum_{cyc} (x^2+2yz)(x-y)^2] -\frac{1}{3}(x+y+z)^2\cdot \sum_{cyc} (x-y)^2\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73932 (x y z : ℝ) (h : 2 * (x * y + y * z + z * x) ≥ x ^ 2 + y ^ 2 + z ^ 2) : (5 * (x ^ 2 + 2 * y * z) * (x - y) ^ 2 + 5 * (y ^ 2 + 2 * z * x) * (y - z) ^ 2 + 5 * (z ^ 2 + 2 * x * y) * (z - x) ^ 2) - (1 / 3) * (x + y + z) ^ 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) ≥ 0   :=  by sorry
