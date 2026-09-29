-- Prove2me | Theorems.Thm_lean_workbook_plus_28241
-- name    : lean_workbook_plus_28241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/aced60d4-a573-4bfd-9903-b3dfa03e1ff0
-- statement:
--   Let $x\ge y\ge z>0$ . Prove that $\frac{x}{x+y}+\frac{y}{y+z}+\frac{z}{z+x}\ge \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28241 (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∧ z > 0) :
  x / (x + y) + y / (y + z) + z / (z + x) ≥ 3 / 2   :=  by sorry
