-- Prove2me | Theorems.Thm_lean_workbook_plus_23812
-- name    : lean_workbook_plus_23812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/200adf6e-961a-4049-b06e-c7c24f3dde2a
-- statement:
--   Let $a,b,c>0$ such that $a^2+b^2+c^2=1.$ Prove that \n $$\frac{a^{3}}{2b+3c}+\frac{b^3}{2c+3a}+\frac{c^{3}}{2a+3b}\geq \frac{1}{5}. $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^3 / (2 * b + 3 * c) + b^3 / (2 * c + 3 * a) + c^3 / (2 * a + 3 * b) ≥ 1 / 5   :=  by sorry
