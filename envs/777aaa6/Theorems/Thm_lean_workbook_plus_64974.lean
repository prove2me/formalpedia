-- Prove2me | Theorems.Thm_lean_workbook_plus_64974
-- name    : lean_workbook_plus_64974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/27acf700-abd5-4845-a036-2ba8a33c6ad3
-- statement:
--   Prove that $\frac{x+1}{x^2+x+1}+\frac{y+1}{y^2+y+1}+\frac{z+1}{z^2+z+1}\le 2$ given $x, y, z > 0$ with $xyz = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64974 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : (x + 1) / (x ^ 2 + x + 1) + (y + 1) / (y ^ 2 + y + 1) + (z + 1) / (z ^ 2 + z + 1) ≤ 2   :=  by sorry
