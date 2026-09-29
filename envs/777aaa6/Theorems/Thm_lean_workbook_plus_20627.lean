-- Prove2me | Theorems.Thm_lean_workbook_plus_20627
-- name    : lean_workbook_plus_20627
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cd524980-e860-4260-b3ed-908ee3dc1f8d
-- statement:
--   Calculate $ \lim_{n\to\infty } \left( e^{1+1/2+1/3+\cdots +1/n+1/(n+1)} -e^{1+1/2+1/3+\cdots +1/n} \right) . $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20627 (n : ℕ) : (exp (∑ k in Finset.range (n + 1), (1 : ℝ) / (k + 1)) - exp (∑ k in Finset.range n, (1 : ℝ) / (k + 1))) = exp (∑' k : ℕ, (1 : ℝ) / (k + 1)) - exp (∑' k : ℕ, (1 : ℝ) / (k + 1))   :=  by sorry
