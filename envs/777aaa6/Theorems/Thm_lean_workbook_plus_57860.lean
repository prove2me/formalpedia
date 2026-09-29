-- Prove2me | Theorems.Thm_lean_workbook_plus_57860
-- name    : lean_workbook_plus_57860
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b5af74b6-2e19-466f-9107-e4fd88546908
-- statement:
--   $ \sum_{k=0}^{\infty} r^k \sum_{i=0}^{k} b_i a_{k-i}\sin((k-2i)\theta)+\sum_{n = 0}^{\infty} |c_n|^2r^{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57860 (a b : ℕ → ℝ) (c : ℕ → ℂ) (θ r : ℝ) :  ∑' k : ℕ, (∑ i in Finset.range (k+1), b i * a (k - i) * Real.sin ((k - 2 * (i : ℝ)) * θ)) * r ^ k + ∑' n : ℕ, ‖c n‖ ^ 2 * r ^ (2 * n) =  ∑' k : ℕ, (∑ i in Finset.range (k+1), b i * a (k - i) * Real.sin ((k - 2 * (i : ℝ)) * θ)) * r ^ k + ∑' n : ℕ, ‖c n‖ ^ 2 * r ^ (2 * n)   :=  by sorry
