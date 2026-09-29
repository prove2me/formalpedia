-- Prove2me | Theorems.Thm_lean_workbook_plus_8296
-- name    : lean_workbook_plus_8296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1c6a163e-77d5-4c84-930a-1a1edf402802
-- statement:
--   Let $ a,b,c>0$ and $ a^2+b^2+c^2=1$ prove that \n $ a+b+c+\frac{1}{abc}\ge \frac{4\sqrt{3}}{9}(a+b+c)(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8296 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a + b + c + 1 / (a * b * c) ≥ (4 * Real.sqrt 3 / 9) * (a + b + c) * (1 / a + 1 / b + 1 / c)   :=  by sorry
