-- Prove2me | Theorems.Thm_lean_workbook_plus_62311
-- name    : lean_workbook_plus_62311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c76c2c2e-a811-4476-87ce-532ce4b05c07
-- statement:
--   Let $x\ge y\ge z>0$ . Prove that $\frac{x}{x+y}+\frac{y}{y+z}+\frac{z}{z+x}\ge \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62311 (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∧ z > 0) : (x / (x + y) + y / (y + z) + z / (z + x)) ≥ 3 / 2   :=  by sorry
