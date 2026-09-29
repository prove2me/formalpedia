-- Prove2me | Theorems.Thm_lean_workbook_plus_37219
-- name    : lean_workbook_plus_37219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7a1acad6-524a-4e4a-9a25-70f1f709b0f5
-- statement:
--   Prove that there exists a subsequence $(x_{n_k})$ of a Cauchy sequence $(x_n)$ such that for all $k > 0$, $|x_{n_{k + 1}} - x_{n_k}| < \frac{1}{2^k}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37219 (x : ℕ → ℝ) (hx : CauchySeq x) :
    ∃ n : ℕ → ℕ, ∀ k : ℕ, k > 0 → |x (n (k + 1)) - x (n k)| < 1 / 2 ^ k   :=  by sorry
