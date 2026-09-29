-- Prove2me | Theorems.Thm_lean_workbook_plus_67127
-- name    : lean_workbook_plus_67127
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/05370a01-d926-49e5-8664-ab96f804a167
-- statement:
--   Find a closed-form formula for the following sequence: $ a_n = \frac {2}{n}(a_1 + \cdots + a_{n - 1}) + kn$ (in terms of $ k$ and $ a_1$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67127 (a : ℕ → ℝ) (k : ℝ) (a1 : ℝ) (h : a = fun (n : ℕ) ↦ 2 / n * (∑ i in Finset.range n, a i) + k * n) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
