-- Prove2me | Theorems.Thm_lean_workbook_plus_25675
-- name    : lean_workbook_plus_25675
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/41a2051b-709f-42b7-8dc6-b4666b551986
-- statement:
--   If $\lim_{x\to\infty}\left(1+\frac{a}{x}-\frac{4}{x^2}\right)^{2x}=e^3$ , find the value of $a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25675 (a : ℝ) (h : ∀ x : ℝ, x > 0 → (1 + a / x - 4 / x ^ 2) ^ (2 * x) = e ^ 3) : a = 3 / 2   :=  by sorry
