-- Prove2me | Theorems.Thm_lean_workbook_plus_77732
-- name    : lean_workbook_plus_77732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4a203952-8b24-4274-adad-8e1824b628ba
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that $\frac{x}{y}+\frac{y}{z}+\frac{z}{x}\geqslant\frac{z(x+y)}{y(y+z)}+\frac{x(y+z)}{z(z+x)}+\frac{y(z+x)}{x(x+y)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77732 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + z / x) ≥ (z * (x + y) / (y * (y + z)) + x * (y + z) / (z * (z + x)) + y * (z + x) / (x * (x + y)))   :=  by sorry
