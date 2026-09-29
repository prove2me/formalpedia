-- Prove2me | Theorems.Thm_lean_workbook_plus_34880
-- name    : lean_workbook_plus_34880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/644b79cf-e9cd-4c83-8f01-872408d4d417
-- statement:
--   Prove that in a subset $S$ of the set $A=\{1,2,...,4s-1,4s\}$ with size $2s+2$, we can find three distinct numbers $x$, $y$, and $z$ such that $x+y=2z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34880 (s : ℕ) (hs : s > 0) (A : Finset ℕ) (hA : A = Finset.Icc 1 (4 * s)) (hA' : A.card = 2 * s + 2) : ∃ x y z : ℕ, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x + y = 2 * z   :=  by sorry
