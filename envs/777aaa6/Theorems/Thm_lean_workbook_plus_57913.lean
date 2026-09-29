-- Prove2me | Theorems.Thm_lean_workbook_plus_57913
-- name    : lean_workbook_plus_57913
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/549bd597-1f5e-49ba-a84e-b32d298f5893
-- statement:
--   Given a set $M$ of $1985$ distinct positive integers, none of which has a prime divisor greater than $23$ , prove that $M$ contains a subset of $4$ elements whose product is the $4$ th power of an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57913 (M : Finset ℕ) (Mpos : ∀ m ∈ M, 0 < m)
    (Mdivisors : ∀ m ∈ M, ∀ n, m.Prime ∧ n ∣ m → m ≤ 23)
    : ∃ M' : Finset ℕ, M' ⊆ M ∧ ∃ k, M'.prod id = k^4   :=  by sorry
