-- Prove2me | Theorems.Thm_lean_workbook_plus_51752
-- name    : lean_workbook_plus_51752
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ef8b19bf-ae6e-406d-982e-c2c0afa04845
-- statement:
--   Prove that $\left(1-\frac{1}{2^2}\right)\left(1-\frac{1}{3^2}\right)\left(1-\frac{1}{4^2}\right)\ldots\left(1-\frac{1}{n^2}\right)=\frac{n+1}{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51752 : ∀ n : ℕ, (∏ k in Finset.Icc 2 n, (1 - 1 / k ^ 2)) = (n + 1) / (2 * n)   :=  by sorry
