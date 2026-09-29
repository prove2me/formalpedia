-- Prove2me | Theorems.Thm_lean_workbook_plus_24343
-- name    : lean_workbook_plus_24343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d67efedb-d33e-4ac5-ac0b-8d1b4a998ed5
-- statement:
--   Given a set A of finitely many primes. Prove that there are only finitely many $n$ such that any prime dividing $n$ or $n+1$ belongs to A.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24343 (A : Finset ℕ) (hA : ∀ a ∈ A, a.Prime) : {n : ℕ | ∀ p : ℕ, p ∣ n ∨ p ∣ n + 1 → p ∈ A}.Finite   :=  by sorry
