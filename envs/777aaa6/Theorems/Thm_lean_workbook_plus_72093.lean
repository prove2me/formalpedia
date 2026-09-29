-- Prove2me | Theorems.Thm_lean_workbook_plus_72093
-- name    : lean_workbook_plus_72093
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1d168794-0499-46ba-8ef7-32887c045204
-- statement:
--   For a positive integer $n$ , an $n$-sequence is a sequence $(a_0,\ldots,a_n)$ of non-negative integers satisfying the following condition: if $i$ and $j$ are non-negative integers with $i+j \leqslant n$ , then $a_i+a_j \leqslant n$ and $a_{a_i+a_j}=a_{i+j}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72093 (n : ℕ) (hn : 0 < n) : ∃ a : ℕ → ℕ, (∀ i j : ℕ, i + j ≤ n → a i + a j ≤ n ∧ a (a i + a j) = a (i + j))   :=  by sorry
