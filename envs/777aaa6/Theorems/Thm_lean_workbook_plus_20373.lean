-- Prove2me | Theorems.Thm_lean_workbook_plus_20373
-- name    : lean_workbook_plus_20373
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5c301cea-151c-4d87-8f88-af057463e401
-- statement:
--   Let a polynomial $P(x) \in Z[x]$ is equal for $n+1$ values of distinct $x$ . Prove that $P(x)$ is constant polynomial.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20373 (n : ℕ) (P : Polynomial ℤ) (hP : P.degree ≤ n) (x : ℕ → ℤ) (hx : ∀ i, x i ≠ x j) (hP_eq : ∀ i : ℕ, i ≤ n → P.eval (x i) = P.eval (x (i + 1))) : P = C (P.eval (x 0))   :=  by sorry
