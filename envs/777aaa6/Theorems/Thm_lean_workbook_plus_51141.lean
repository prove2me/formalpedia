-- Prove2me | Theorems.Thm_lean_workbook_plus_51141
-- name    : lean_workbook_plus_51141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/87571538-b1e9-4da6-81c4-18bda14d450a
-- statement:
--   Let $f$ be the multiplicative arithmetic function defined by $f(1)=1$ and $f(p^a)=pf(a)$ for all primes $p$ and all positive integers $a$. Prove that $f(n)\leq n$ for all $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51141 {f : ℕ → ℕ} (hf : f 1 = 1 ∧ ∀ p a : ℕ, Nat.Prime p → f (p^a) = p * f a) : ∀ n : ℕ, f n ≤ n   :=  by sorry
