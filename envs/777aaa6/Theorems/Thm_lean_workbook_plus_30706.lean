-- Prove2me | Theorems.Thm_lean_workbook_plus_30706
-- name    : lean_workbook_plus_30706
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ca7135f7-bd08-4c6a-8ea4-1bb8e4268de1
-- statement:
--   Let $a_n$ be the number of strings of length $n$ that end in $0$ and $b_n$ be the number of strings of length $n$ that end in $1$ . Then $b_{n+1} = b_n + a_n $ and $a_{n+1}= a_n +b_{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30706 (a b : ℕ → ℕ) (n : ℕ) (h₁ : b (n + 1) = b n + a n) (h₂ : a (n + 1) = a n + b (n - 1)) : b (n + 1) = b n + a n ∧ a (n + 1) = a n + b (n - 1)   :=  by sorry
