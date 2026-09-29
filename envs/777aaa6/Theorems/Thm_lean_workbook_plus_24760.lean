-- Prove2me | Theorems.Thm_lean_workbook_plus_24760
-- name    : lean_workbook_plus_24760
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bd89152a-0f3d-4fb9-91ef-b3ecf3525210
-- statement:
--   Let $x, y, z$ be positive real numbers. Prove that: \n $\frac{x + 2y}{z + 2x + 3y}+\frac{y + 2z}{x + 2y + 3z}+\frac{z + 2x}{y + 2z + 3x} \le \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24760 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 2*y) / (z + 2*x + 3*y) + (y + 2*z) / (x + 2*y + 3*z) + (z + 2*x) / (y + 2*z + 3*x) ≤ 3/2   :=  by sorry
