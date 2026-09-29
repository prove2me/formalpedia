-- Prove2me | Theorems.Thm_lean_workbook_plus_55065
-- name    : lean_workbook_plus_55065
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2b477afe-0b79-4aa2-8e59-26462facb7cc
-- statement:
--   Given a sequence $ a_1,a_2,...,a_{99}$ of one-digit numbers with the poperty that if for some $ n$ we have $ a_n = 1$ , then $ a_{n + 1}\neq 2$ ; and if for some $ n$ we have $ a_n = 3$ , then $ a_{n + 1}\neq 4$ . Prove that exist two number $ k,l\in\{1,2,...,98\}$ such that $ a_k = a_l$ and $ a_{k + 1} = a_{l + 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55065 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n ∧ a n <= 9) (h₁ : ∀ n, a n = 1 → a (n + 1) ≠ 2) (h₂ : ∀ n, a n = 3 → a (n + 1) ≠ 4) : ∃ k l, k ∈ Finset.Icc 1 98 ∧ l ∈ Finset.Icc 1 98 ∧ a k = a l ∧ a (k + 1) = a (l + 1)   :=  by sorry
