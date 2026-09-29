-- Prove2me | Theorems.Thm_lean_workbook_plus_20500
-- name    : lean_workbook_plus_20500
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/31ab12e2-d220-45fc-a14a-fadea91a45b3
-- statement:
--   Find the value of: $\frac{1}{1 \times 3} + \frac{1}{2 \times 4} + ... + \frac{1}{7 \times 9}+ \frac{1}{8 \times 10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20500 (h : ∀ n : ℕ, (1 : ℝ) / (n * (n + 2)) = (1 : ℝ) / n - (1 : ℝ) / (n + 2)) : ∑ k in Finset.Icc (1 : ℕ) 8, (1 : ℝ) / (k * (k + 2)) = 29 / 45   :=  by sorry
