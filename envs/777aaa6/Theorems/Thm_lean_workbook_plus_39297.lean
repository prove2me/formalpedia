-- Prove2me | Theorems.Thm_lean_workbook_plus_39297
-- name    : lean_workbook_plus_39297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/60970cab-72ab-49ea-8a40-1edab3f3301c
-- statement:
--   Let $\{x_n\} $ be a sequence of real numbers with the property that for any $n\geq 2$ $\exists\ k,$ $\frac{n}{2}<k <n $ , such that $x_n=\frac{x_k }{2}$ , prove that $\lim\limits_{n\to\infty} x_n=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39297 (x : ℕ → ℝ) (hx : ∀ n ≥ 2, ∃ k, n / 2 < k ∧ k < n ∧ x n = x k / 2) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n| < ε   :=  by sorry
