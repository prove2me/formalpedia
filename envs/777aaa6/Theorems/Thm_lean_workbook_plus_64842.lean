-- Prove2me | Theorems.Thm_lean_workbook_plus_64842
-- name    : lean_workbook_plus_64842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/93cb3cc3-e12d-4ede-a6aa-f6337363445a
-- statement:
--   Given positive integers $k$ and $m$ , show that $m$ and $\binom{n}{k}$ are coprime for infinitely many integers $n\geq k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64842 (k m : ℕ) (h₁ : 0 < k ∧ 0 < m) (h₂ : m ≤ k) : ∃ n, n ≥ k ∧ Nat.Coprime m (Nat.choose n k)   :=  by sorry
