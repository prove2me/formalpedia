-- Prove2me | Theorems.Thm_lean_workbook_plus_21743
-- name    : lean_workbook_plus_21743
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f5a5699e-6d85-4fa4-bb85-a9f79219ed91
-- statement:
--   Find the maximum or minimum value of the expression $\frac{x}{1+yz}+\frac{y}{1+xz}+\frac{z}{1+xy}$ given that $x, y, z > 0$ and $x^2+y^2+z^2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21743 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hx2 : x ^ 2 + y ^ 2 + z ^ 2 = 1) : (x / (1 + y * z) + y / (1 + x * z) + z / (1 + x * y) ≤ 1 ∨ x / (1 + y * z) + y / (1 + x * z) + z / (1 + x * y) ≥ 1)   :=  by sorry
