-- Prove2me | Theorems.Thm_lean_workbook_plus_58272
-- name    : lean_workbook_plus_58272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5c7a03cd-b28e-4501-8841-0acd50f876f1
-- statement:
--   Find all functions $f$ : $\mathbb{N} \rightarrow \mathbb{N}$ such that $f(2n)=f(n)+f(n-1)$, $f(2n+1)=f(n)$, and $f(0)=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58272 (f : ℕ → ℕ) (h₁ : f 0 = 1) (h₂ : ∀ n, f (2 * n) = f n + f (n - 1)) (h₃ : ∀ n, f (2 * n + 1) = f n) : ∀ n, f n = fib (n + 1)   :=  by sorry
