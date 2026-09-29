-- Prove2me | Theorems.Thm_lean_workbook_plus_78314
-- name    : lean_workbook_plus_78314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7594cb70-9e32-477f-a003-45e8d952a2e2
-- statement:
--   Derive the inequality $\frac{a^2}{b^2} + 1 \le \frac{5a}{2b}$ from $\left( \frac{a}{b} - \frac{1}{2} \right) \left( \frac{a}{b} -2 \right) \le 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78314 (a b : ℝ) (hab : b ≠ 0) (h : (a / b - 1 / 2) * (a / b - 2) ≤ 0) :
  a^2 / b^2 + 1 ≤ 5 * a / (2 * b)   :=  by sorry
