-- Prove2me | Theorems.Thm_lean_workbook_plus_30124
-- name    : lean_workbook_plus_30124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b76a98a1-9543-41d3-a875-d3de5daa16ea
-- statement:
--   Let $f(0)=a$ and $f(1)=b$, then $f(2n)=2n+a$ and $f(2n+1)=2n+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30124 (a b : ℝ) (f : ℕ → ℝ) (h₀ : f 0 = a) (h₁ : f 1 = b) (h₂ : ∀ n, f (2 * n) = 2 * n + a) (h₃ : ∀ n, f (2 * n + 1) = 2 * n + b) : ∃ a b, f 0 = a ∧ f 1 = b ∧ (∀ n, f (2 * n) = 2 * n + a) ∧ (∀ n, f (2 * n + 1) = 2 * n + b)   :=  by sorry
