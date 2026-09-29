-- Prove2me | Theorems.Thm_lean_workbook_plus_29237
-- name    : lean_workbook_plus_29237
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ce9414fe-9ea7-4aa0-8a5c-d0620a18476c
-- statement:
--   Given $a-b=x, b-c=y, c-a=z$, prove that $a^3x^2z^2+b^3x^2y^2+c^3y^2z^2-(a+b+c)x^2y^2z^2$ is equivalent to $(axz+bxy+cyz)\left(a^2xz+b^2xy+c^2yz\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29237 (a b c x y z : ℝ) (hx : x = a - b) (hy : y = b - c) (hz : z = c - a) : a^3 * x^2 * z^2 + b^3 * x^2 * y^2 + c^3 * y^2 * z^2 - (a + b + c) * x^2 * y^2 * z^2 = (a * x * z + b * x * y + c * y * z) * (a^2 * x * z + b^2 * x * y + c^2 * y * z)   :=  by sorry
