-- Prove2me | Theorems.Thm_lean_workbook_plus_19738
-- name    : lean_workbook_plus_19738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e3578724-d8e5-4eb5-8249-6185c02a24f9
-- statement:
--   Let $n \in \mathbb{N}$ and $a_1, a_2, ..., a_{n+1} \in \mathbb{N} $ so that $a_1, a_2, ..., a_{n+1} < 2n$ ( and every two of these numbers are different). Prove that between this $n+1$ numers we can find $3$ , say $a,b,c $ , so that $a+b = c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19738 (n : ℕ) (A: Finset ℕ) (hA: A.card = n+1) (hA2: ∀ a ∈ A, a < 2*n) (hA3: ∀ a ∈ A, ∀ b ∈ A, a ≠ b): ∃ a b c: ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a+b = c   :=  by sorry
