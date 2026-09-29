-- Prove2me | Theorems.Thm_lean_workbook_plus_18821
-- name    : lean_workbook_plus_18821
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/57631f1f-5fbc-42d3-b54a-500ccc29a6d5
-- statement:
--   e) $ {LHS - RHS}|_{(a;b;c) = (x + y;y + z;z + x), 0\leq x\leq y\leq z}$\n $ = 2(y - x)(z - x)(145(y - x)(z - x) + 59(z - y)^2) +$\n $ + 2x(z + y - 2x)(461(y - x)(z - x) + 98(z - y)^2) +$\n $ + 204x^2(21(y - x)(z - x) + 5(z - y)^2) + 2176x^3(z + y - 2x) +$\n $ + 10(z - y)^4 + 1632x^4\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18821 (x y z : ℝ) (h1 : 0 ≤ x) (h2 : 0 ≤ y) (h3 : 0 ≤ z) (h4 : x ≤ y) (h5 : y ≤ z) (h6 : z ≤ x + y) (h7 : 0 ≤ y - x) (h8 : 0 ≤ z - x) (h9 : 0 ≤ z - y) : 2 * (y - x) * (z - x) * (145 * (y - x) * (z - x) + 59 * (z - y) ^ 2) + 2 * x * (z + y - 2 * x) * (461 * (y - x) * (z - x) + 98 * (z - y) ^ 2) + 204 * x ^ 2 * (21 * (y - x) * (z - x) + 5 * (z - y) ^ 2) + 2176 * x ^ 3 * (z + y - 2 * x) + 10 * (z - y) ^ 4 + 1632 * x ^ 4 ≥ 0   :=  by sorry
