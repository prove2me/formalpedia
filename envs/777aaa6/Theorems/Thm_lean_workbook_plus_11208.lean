-- Prove2me | Theorems.Thm_lean_workbook_plus_11208
-- name    : lean_workbook_plus_11208
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8333a243-613f-419e-ab75-0cbf49a4f73f
-- statement:
--   Find a sufficient condition for the inequality $\sum_{i = 1} ^n \sum_{sym} x^{a_{2i - 1}}y^{a_{2i}} \ge \sum_{i = 1} ^n \sum_{sym} x^{b_{2i - 1}}y^{b_{2i}}$ to hold for all $x,y \in \mathbb{R}^+$, where $\sum a_i = \sum b_i$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11208 (n : ℕ) (a b : ℕ → ℕ) (hab : a = b) : ∀ x y : ℝ, ∑ i in Finset.range n, ∑ j in Finset.range 2, x ^ a (2 * i + j) * y ^ a (2 * i + 1) ≥ ∑ i in Finset.range n, ∑ j in Finset.range 2, x ^ b (2 * i + j) * y ^ b (2 * i + 1)   :=  by sorry
