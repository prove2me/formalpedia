-- Prove2me | Theorems.Thm_lean_workbook_plus_77896
-- name    : lean_workbook_plus_77896
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/521707e4-3779-48d5-950e-2c99cc1bfc11
-- statement:
--   Find the general formulas of $a_n$ given $a_1=1,a_2=1$ and $a_n=\frac{\Sigma^{n-1}_{k=1}C^k_na_ka_{n-k}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77896 (n : ℕ) (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1) (a_rec : ∀ n, a n = (∑ k in Finset.range (n-1), (n.choose k) * a k * a (n-k)) / 2) : a n = (2 * n - 3)!!   :=  by sorry
