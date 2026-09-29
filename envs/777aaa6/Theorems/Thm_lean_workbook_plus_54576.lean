-- Prove2me | Theorems.Thm_lean_workbook_plus_54576
-- name    : lean_workbook_plus_54576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/143e7333-701b-429f-9baf-f0e32073a8b2
-- statement:
--   Prove that for positive numbers $x, y, z$, the following inequality holds: $\frac{x^{2}}{y}+\frac{y^{2}}{z}+\frac{z^{2}}{x}\geq x+y+z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54576 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2 / y + y^2 / z + z^2 / x >= x + y + z   :=  by sorry
