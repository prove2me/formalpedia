-- Prove2me | Theorems.Thm_lean_workbook_plus_44938
-- name    : lean_workbook_plus_44938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fa508a7a-71fe-4dd8-9509-1fc86284a099
-- statement:
--   Prove that:\n$ 8(x^3 + y^3 + z^3)^2 \geq 9(x^2 + yz)(y^2 + zx)(z^2 + xy)$\nWhere $ x,y,z$ are arbitrary positive reals
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44938 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)   :=  by sorry
