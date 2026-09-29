-- Prove2me | Theorems.Thm_lean_workbook_plus_5124
-- name    : lean_workbook_plus_5124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c894d6d0-4be1-42e7-a301-2c518b9b7543
-- statement:
--   If $x, y, z$ are positive real numbers, prove that $(x+y+z)^2(yz+zx+xy)^2 \leq 3(y^2+yz+z^2)(z^2+zx+x^2)(x^2+xy+y^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5124 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (y * z + z * x + x * y) ^ 2 ≤ 3 * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2)   :=  by sorry
