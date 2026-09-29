-- Prove2me | Theorems.Thm_lean_workbook_plus_68371
-- name    : lean_workbook_plus_68371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0ab9a320-1dc2-4a53-bbc4-efbc9d29e3dd
-- statement:
--   Prove that $\frac{a^2}{x}+\frac{b^2}{y}\geq \frac{(a+b)^2}{x+y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68371 (a b x y : ℝ) (hx : x > 0) (hy : y > 0) : (a^2 / x + b^2 / y) ≥ (a + b)^2 / (x + y)   :=  by sorry
