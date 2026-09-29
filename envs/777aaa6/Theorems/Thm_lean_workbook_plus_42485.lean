-- Prove2me | Theorems.Thm_lean_workbook_plus_42485
-- name    : lean_workbook_plus_42485
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/54a95beb-0e75-4052-a981-b76e073c1709
-- statement:
--   Given $m > n$ and $gcd(2^n, 2^n - 1) = 1$, prove that $2^n - 1$ divides $2^{m-n} + 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42485 : ∀ m n : ℕ, m > n ∧ Nat.gcd (2 ^ n) (2 ^ n - 1) = 1 → (2 ^ n - 1) ∣ (2 ^ (m - n) + 1)   :=  by sorry
