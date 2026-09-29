-- Prove2me | Theorems.Thm_lean_workbook_plus_16577
-- name    : lean_workbook_plus_16577
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e68d6aed-3894-4e7e-b4ff-3d73ece46d34
-- statement:
--   Let $0<x_n<\frac{1}{n}$ such that $\sum_{n\geq 1}{x_n}$ converges. Then $\sum_{n\geq 1}{\frac{x_n}{1-nx_n}}$ also converges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16577 (x : ℕ → ℝ) (hx : ∀ n, 0 < x n ∧ x n < 1 / n) (h : Summable x) : Summable (fun n => x n / (1 - n * x n))   :=  by sorry
