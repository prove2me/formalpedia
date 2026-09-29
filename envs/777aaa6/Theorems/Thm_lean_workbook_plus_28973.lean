-- Prove2me | Theorems.Thm_lean_workbook_plus_28973
-- name    : lean_workbook_plus_28973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1aba9d27-3541-4a2d-891a-f163a7b2a095
-- statement:
--   Prove that if $\lim_{n\to \infty} x_n^{1/n} = d < 1$, then $\lim_{n\to \infty} x_n = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28973 (x : ℕ → NNReal) (d : ℝ) (hd : d < 1) (h : ∀ n, (x n)^(1/n) = d) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x n < ε   :=  by sorry
