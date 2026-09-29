-- Prove2me | Theorems.Thm_lean_workbook_plus_25841
-- name    : lean_workbook_plus_25841
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0bad91bb-6e2b-4ebc-bbc4-686cdf6cba74
-- statement:
--   Does the statement 'there exists $k$ such that for all $n \ge k$, $f(n) \ge \frac{1}{2}$' hold for a function $f(n)$ that converges to 1 as $n$ approaches infinity?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25841 (f : ℕ → ℝ) (h : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |f n - 1| < ε) : ∃ k : ℕ, ∀ n : ℕ, n ≥ k → f n ≥ 1 / 2   :=  by sorry
