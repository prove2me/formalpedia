-- Prove2me | Theorems.Thm_lean_workbook_plus_26994
-- name    : lean_workbook_plus_26994
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c4254821-7a8b-4311-8d4c-830a1e242c56
-- statement:
--   Find the value of $\displaystyle\sum_{i = 7}^{100}{(\frac{2}{3})^i}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26994 (x : ℝ) (hx : x = ∑ i in (Finset.Icc 7 100), (2/3)^i) : x = 5350.666666666666   :=  by sorry
