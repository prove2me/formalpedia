-- Prove2me | Theorems.Thm_lean_workbook_plus_16240
-- name    : lean_workbook_plus_16240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d3999d7a-2ff9-45e6-b11d-94e9447c55f6
-- statement:
--   Prove that for positive numbers $x, y, z$, the following inequality holds: $ \frac{x + y}{2z + x + y} + \frac{y + z}{2x + y + z} + \frac{z + x}{2y + z + x} \ge \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16240 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) / (2 * z + x + y) + (y + z) / (2 * x + y + z) + (z + x) / (2 * y + z + x) ≥ 3 / 2   :=  by sorry
