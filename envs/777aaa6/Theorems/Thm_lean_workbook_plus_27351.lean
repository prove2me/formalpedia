-- Prove2me | Theorems.Thm_lean_workbook_plus_27351
-- name    : lean_workbook_plus_27351
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/75ffcb0a-6a2f-4b0e-b133-11f6e2af91fc
-- statement:
--   Let $a,b,c>0$ such that $\sum_{cyc}a^2b^2\sum_{cyc}\frac{1}{a^3}=4$ . Prove that:\n\n $\frac{ab}{b+c^2}+\frac{bc}{c+a^2}+\frac{ca}{a+b^2}\geq a+b+c-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27351 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) (h : a^2 * b^2 * (1 / a^3 + 1 / b^3 + 1 / c^3) = 4) : a * b / (b + c^2) + b * c / (c + a^2) + c * a / (a + b^2) ≥ a + b + c - 1   :=  by sorry
