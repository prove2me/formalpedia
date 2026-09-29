-- Prove2me | Theorems.Thm_lean_workbook_plus_53186
-- name    : lean_workbook_plus_53186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/84386d78-bf15-4c28-b638-39c35f8d83c2
-- statement:
--   Let $a$ , $b$ be integers greater than $2$ . Prove that there exists a positive integer $k$ and a finite sequence $n_1, n_2, . . . , n_k$ of positive integers such that $n_1=a$ , $n_k=b$ , and $n_{i}n_{i+1}$ is divisible by $n_i+n_{i+1}$ for each $i$ $(1\le i < k)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53186 (a b : ℤ) (hab : 2 < a ∧ 2 < b) :
    ∃ k : ℕ, ∃ n : ℕ → ℤ,
      n 0 = a ∧ n k = b ∧
      ∀ i, 0 < i ∧ i < k → (n i + n (i + 1)) ∣ n i * n (i + 1)   :=  by sorry
