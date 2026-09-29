-- Prove2me | Theorems.Thm_lean_workbook_plus_55433
-- name    : lean_workbook_plus_55433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ada3149f-ba0c-4368-a414-e0b5b797df4a
-- statement:
--   Prove that for positive real numbers x, y, and z, the following inequality holds:\n$\frac{(2x + 2y + 2z)^2}{3(x + y)^2 + 3(y + z)^2 + 3(z + x)^2} \geq \frac{9}{16}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55433 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x + 2 * y + 2 * z) ^ 2 / (3 * (x + y) ^ 2 + 3 * (y + z) ^ 2 + 3 * (z + x) ^ 2) ≥ 9 / 16   :=  by sorry
