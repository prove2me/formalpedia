-- Prove2me | Theorems.Thm_lean_workbook_plus_12581
-- name    : lean_workbook_plus_12581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5b31e775-6429-4191-86f9-35ee3417089c
-- statement:
--   Prove that if a sequence $x_n$ converges to $x$ and $f$ is a continuous function, then $f(x_n)$ converges to $f(x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12581 (x : ℕ → ℝ) (f : ℝ → ℝ) (hf: Continuous f) (hx: ∃ a, ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε) : ∃ a, ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |f (x n) - a| < ε   :=  by sorry
