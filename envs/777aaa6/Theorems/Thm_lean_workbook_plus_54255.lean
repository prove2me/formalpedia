-- Prove2me | Theorems.Thm_lean_workbook_plus_54255
-- name    : lean_workbook_plus_54255
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0790aab5-50a4-40f9-a78a-eeca29ed0a5b
-- statement:
--   Prove the inequality with Jensen's inequality: \n$x,y,z$ are Positive Real, prove that: \n$$\frac{x^2}{x+y}+\frac{y^2}{y+z}+\frac{z^2}{z+x}\ge\frac{x+y+z}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54255 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 / (x + y) + y^2 / (y + z) + z^2 / (z + x)) ≥ (x + y + z) / 2   :=  by sorry
