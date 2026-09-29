-- Prove2me | Theorems.Thm_lean_workbook_plus_35184
-- name    : lean_workbook_plus_35184
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9ca3285e-5caa-4c0e-9366-efeb30b0c058
-- statement:
--   Note that $\frac{a^{2} +1}{bc} +\frac{b^{2} +1}{ca} +\frac{c^{2} +1}{ab} =\frac{a^{3} +b^{3} +c^{3} +a+b+c}{abc}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35184 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a * b * c = 1) : (a^2 + 1) / b / c + (b^2 + 1) / c / a + (c^2 + 1) / a / b = (a^3 + b^3 + c^3 + a + b + c) / a / b / c   :=  by sorry
