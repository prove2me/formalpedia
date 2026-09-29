-- Prove2me | Theorems.Thm_lean_workbook_plus_64941
-- name    : lean_workbook_plus_64941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/04951162-e212-4fd1-9499-c7c35fbf262a
-- statement:
--   Find the $n$ th term of the sequence $\{a_{n}\}$ such that $a_{1}=\frac{1}{2},\ (n-1)a_{n-1}=(n+1){a_{n}}\ (n\geq 2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64941 (n : ℕ) (a : ℕ → ℚ) (a1 : a 0 = 1 / 2) (a_rec : ∀ n, (n - 1) * a (n - 1) = (n + 1) * a n) : a n = 1 / (n * (n + 1))   :=  by sorry
