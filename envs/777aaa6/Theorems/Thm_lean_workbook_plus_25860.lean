-- Prove2me | Theorems.Thm_lean_workbook_plus_25860
-- name    : lean_workbook_plus_25860
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b20857e5-c414-461d-9c9e-cb3457ead994
-- statement:
--   Given $x_1 + x_2 + \cdots + x_n + \frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_n} \ge 2n$, prove that either $x_1+x_2 + \cdots + x_n \geq n$ or $\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_n} \ge n$ is true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25860 (n : ℕ) (x : ℕ → ℝ) (hx : ∀ i, x i > 0) : (∑ i in Finset.range n, x i + ∑ i in Finset.range n, (1 / x i)) ≥ 2 * n → (∑ i in Finset.range n, x i) ≥ n ∨ (∑ i in Finset.range n, (1 / x i)) ≥ n   :=  by sorry
