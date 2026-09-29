-- Prove2me | Theorems.Thm_lean_workbook_plus_2315
-- name    : lean_workbook_plus_2315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e3dc6cc9-56a9-4f78-a7d6-7fb938a49b53
-- statement:
--   Take a Cauchy sequence $\{x_n\}$ and construct a subsequence $\{x_{n_k}\}$ such that $\lVert x_{n_{k+1}}-x_{n_k}\rVert\leq 2^{-k}$ for all $k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2315 (x : ℕ → ℝ) (hx : CauchySeq x) :
    ∃ n : ℕ → ℕ, ∀ k : ℕ, ‖x (n (k + 1)) - x (n k)‖ ≤ (1 / 2)^k   :=  by sorry
