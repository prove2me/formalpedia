-- Prove2me | Theorems.Thm_lean_workbook_plus_9293
-- name    : lean_workbook_plus_9293
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/6f1e8cb2-bd39-4d85-879e-b85c945e1218
-- statement:
--   Let $x,y,z\in\mathbb{R^+}$ .Prove that $$\frac{x+2y}{z+2x+3y}+\frac{y+2z}{x+2y+3z}+\frac{z+2x}{y+2z+3x}>\frac{6}{7}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9293 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + 2 * y) / (z + 2 * x + 3 * y) + (y + 2 * z) / (x + 2 * y + 3 * z) + (z + 2 * x) / (y + 2 * z + 3 * x) > 6 / 7   :=  by sorry
