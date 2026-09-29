-- Prove2me | Theorems.Thm_lean_workbook_plus_17041
-- name    : lean_workbook_plus_17041
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/501b8681-d060-4bb8-a498-69061daec93a
-- statement:
--   Find the value of $\lim_{n\to\infty}\sum_{k=n+1}^{2n}\frac{1}{k}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17041 (n : ℕ) : ∃ l, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ k : ℕ, k > N → |(∑ k in Finset.Icc (n + 1) (2 * n), (1 : ℝ) / k) - l| < ε   :=  by sorry
