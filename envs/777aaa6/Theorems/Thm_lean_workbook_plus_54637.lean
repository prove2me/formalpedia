-- Prove2me | Theorems.Thm_lean_workbook_plus_54637
-- name    : lean_workbook_plus_54637
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d41ca17d-d92f-4320-9b47-984147aef4b5
-- statement:
--   If $a_1,\ldots,a_n$ are positive integers and $1\le a_1\le \ldots \le a_n$ and $a_1^3+\cdots+a_n^3\ge(a_1+\cdots+a_n)^2$ , show that $a_i=i$ for all $i$ from $1$ to $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54637 (n : ℕ) (a : ℕ → ℕ) (ha : ∀ i, 0 < a i) (ha2 : ∀ i, a i ≤ a (i + 1)) (h : ∑ i in Finset.range n, (a i)^3 ≥ (∑ i in Finset.range n, a i)^2) : ∀ i, a i = i   :=  by sorry
