-- Prove2me | Theorems.Thm_lean_workbook_plus_65784
-- name    : lean_workbook_plus_65784
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/62f45486-683c-49a4-bc3a-55cfbf9baeb6
-- statement:
--   Prove that for any positive integer $n$, there exists a positive integer $k$ such that the equation $\sum_{i=1}^k \frac{1}{x_i^n}=1$ has at least one solution, where $x_1, x_2, \dots, x_k$ are positive integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65784 (n : ℕ) : ∃ k : ℕ, ∃ x : ℕ → ℕ, (∑ i in Finset.range k, (1/(x i))^n) = 1   :=  by sorry
