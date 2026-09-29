-- Prove2me | Theorems.Thm_lean_workbook_plus_32146
-- name    : lean_workbook_plus_32146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6dc64cde-a989-4b3a-94cf-59357deffed1
-- statement:
--   Given a sequence $(x_n)$ defined by $x_1=\frac{1}{2}$ and $x_{n+1}=x_n-x_n^2$. Prove that $\sum_{1}^{\infty} x_n$ converges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32146 (x : ℕ → ℝ) (hx : x 1 = 1 / 2 ∧ ∀ n, x (n + 1) = x n - (x n) ^ 2) : Summable x   :=  by sorry
