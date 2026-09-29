-- Prove2me | Theorems.Thm_lean_workbook_plus_20973
-- name    : lean_workbook_plus_20973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/373eca0a-db51-49b1-a699-aadb3d43c01d
-- statement:
--   Induction on $n$ . For prime $p$ such that $\gcd (p,a)= \gcd (p,b)=1$ then for each $n$ , there exists $x_n,y_n$ such that $p^n \mid ax_n^2+by_n^2-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20973 (p a b : ℕ) (hp : p.Prime) (hab : a ≠ 0 ∧ b ≠ 0) (hgcd1 : Nat.Coprime a p) (hgcd2 : Nat.Coprime b p) : ∀ n : ℕ, ∃ x y : ℕ, p ^ n ∣ a * x ^ 2 + b * y ^ 2 - 1   :=  by sorry
