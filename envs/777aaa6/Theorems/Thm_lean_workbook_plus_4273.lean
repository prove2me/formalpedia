-- Prove2me | Theorems.Thm_lean_workbook_plus_4273
-- name    : lean_workbook_plus_4273
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9c461491-0d0d-4964-8a31-d433d62eee73
-- statement:
--   Prove that for all positive integers $ n$ : $ \frac{2n}{3n+1} \le \displaystyle\sum_{k=n+1}^{2n}\frac{1}{k} \le \frac{3n+1}{4(n+1)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4273 : ∀ n : ℕ, (2 * n / (3 * n + 1) : ℝ) ≤ ∑ k in Finset.Icc (n + 1) (2 * n), (1 / k) ∧ ∑ k in Finset.Icc (n + 1) (2 * n), (1 / k) ≤ (3 * n + 1) / (4 * (n + 1))   :=  by sorry
