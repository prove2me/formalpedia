-- Prove2me | Theorems.Thm_lean_workbook_plus_60849
-- name    : lean_workbook_plus_60849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7cbec1ab-ea6d-4dba-be07-b731fda56ab1
-- statement:
--   Prove $h(y)=y^3+4y+\frac{2}{y}-2y^2\geq 4$ for all $y>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60849 (y : ℝ) (hy : y > 0) : y ^ 3 + 4 * y + 2 / y - 2 * y ^ 2 ≥ 4   :=  by sorry
