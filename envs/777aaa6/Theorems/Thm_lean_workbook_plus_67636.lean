-- Prove2me | Theorems.Thm_lean_workbook_plus_67636
-- name    : lean_workbook_plus_67636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f4ca2f6f-e4a5-4ef9-b39e-9a0e581b3fdf
-- statement:
--   Prove that $(\frac{x}{x+y})^2 + (\frac{y}{z+x})^2 + (\frac{z}{y+z})^2 \geq \frac{1}{3}(\frac{x}{x+y}+\frac{y}{z+x}+\frac{z}{y+z})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67636 (x y z : ℝ) :
  (x / (x + y)) ^ 2 + (y / (z + x)) ^ 2 + (z / (y + z)) ^ 2 ≥
    1 / 3 * (x / (x + y) + y / (z + x) + z / (y + z)) ^ 2   :=  by sorry
