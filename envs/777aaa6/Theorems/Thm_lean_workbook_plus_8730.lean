-- Prove2me | Theorems.Thm_lean_workbook_plus_8730
-- name    : lean_workbook_plus_8730
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6b7dc351-dfb2-45cc-9a09-fc16568bd1c1
-- statement:
--   Prove the binomial theorem $(a+b)^n = \sum_{j = 0}^n \dbinom{n}{j}a^{n-j}b^j$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8730 (a b : ℝ) (n : ℕ) : (a + b) ^ n = ∑ j in Finset.range (n + 1), choose n j * a ^ (n - j) * b ^ j   :=  by sorry
