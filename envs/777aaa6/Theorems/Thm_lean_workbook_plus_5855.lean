-- Prove2me | Theorems.Thm_lean_workbook_plus_5855
-- name    : lean_workbook_plus_5855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/adb02716-cdc2-49aa-942d-b328d279003c
-- statement:
--   Prove that $\frac{2}{x+y}+\frac{2}{y+z}+\frac{2}{x+z}\geq\frac{9}{x+y+z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5855 (x y z : ℝ) : (x + y + z > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0) → 2 / (x + y) + 2 / (y + z) + 2 / (x + z) ≥ 9 / (x + y + z)   :=  by sorry
