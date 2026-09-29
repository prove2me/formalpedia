-- Prove2me | Theorems.Thm_lean_workbook_plus_36877
-- name    : lean_workbook_plus_36877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/01542d9e-7366-4b2c-a7e0-1f77c36d14a3
-- statement:
--   Setting $x = {a^2} + {b^2} + {c^2};y = ab + bc + ca$ and rewrite the inequality as the form of $x,y$ . We need to prove $\frac{{3x}}{{4\left( {x + 2y} \right)}} + \frac{3}{4} \le \frac{{2x + 4y}}{{x + 5y}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36877 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : 3 * x / (4 * (x + 2 * y)) + 3 / 4 ≤ 2 * x + 4 * y / (x + 5 * y)   :=  by sorry
