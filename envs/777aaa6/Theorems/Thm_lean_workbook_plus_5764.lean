-- Prove2me | Theorems.Thm_lean_workbook_plus_5764
-- name    : lean_workbook_plus_5764
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9c701eee-a3e3-4a8f-8360-80fe889d5e7f
-- statement:
--   Suppose $n$ is divisible by a prime $p \neq 3$. Write $n=p \ell$ and $t:=2^{\ell}$. Prove that $1+2^n+4^n$ is not prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5764 : ∀ n : ℕ, (∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ n = p * ℓ → ¬Nat.Prime (1 + 2^n + 4^n))   :=  by sorry
