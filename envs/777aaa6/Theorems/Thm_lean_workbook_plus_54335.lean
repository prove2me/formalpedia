-- Prove2me | Theorems.Thm_lean_workbook_plus_54335
-- name    : lean_workbook_plus_54335
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/52a441b9-b300-4f79-aae3-54b6d5bc19e3
-- statement:
--   Let $a_1, a_2, a_3, \ldots$ be a sequence of integers satisfying the inequality $o \le a_n < n$ for every $n$ . Prove that the series $\sum_{n=1}^{\infty} a_n / n!$ is convergent. Prove also that its limit is irrational if and only if $a_n \le n-2$ for infinitely many $n$ and $a_m > 0$ for infinitely many $m$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54335 (a : ℕ → ℤ) (ha : ∀ n, 0 ≤ a n ∧ a n < n) : Summable (λ n => (a n : ℝ) / n!)   :=  by sorry
