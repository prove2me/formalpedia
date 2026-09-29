-- Prove2me | Theorems.Thm_lean_workbook_plus_15983
-- name    : lean_workbook_plus_15983
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a106bbc9-5c48-4562-968b-83192b1cb701
-- statement:
--   If $ x, y$ and $z$ are positive numbers, prove that \n$$\frac{x+y}{z}+\frac{y+z}{x}+\frac{z+x}{y}\ge 2(x+y+z)(\frac{1}{ x}+\frac{1}{y }+\frac{1}{z }).$$ (WISCONSIN MATHEMATICS, SCIENCE & ENGINEERING TALENT SEARCH PROBLEM SET III (2011-2012) DECEMBER 2011)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15983 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) / z + (y + z) / x + (z + x) / y ≥ 2 * (x + y + z) * (1 / x + 1 / y + 1 / z)   :=  by sorry
