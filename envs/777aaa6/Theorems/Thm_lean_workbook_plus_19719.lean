-- Prove2me | Theorems.Thm_lean_workbook_plus_19719
-- name    : lean_workbook_plus_19719
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/737ad78c-0fd9-4df2-a15b-39261a6f2e4f
-- statement:
--   Let $a_{n}=\frac{n^{3}}{n^{2}-15n+75}$ where $n$ is an integer between 1 and 15 inclusive. What is $\sum_{n=1}^{15}a_{n}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19719 (a : ℕ → ℚ) (h : ∀ n, a n = n^3/(n^2 - 15*n + 75)) : ∑ n in Finset.Icc 1 15, a n = 45   :=  by sorry
