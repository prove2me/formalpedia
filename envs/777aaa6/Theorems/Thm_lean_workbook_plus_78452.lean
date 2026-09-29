-- Prove2me | Theorems.Thm_lean_workbook_plus_78452
-- name    : lean_workbook_plus_78452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/aa30e26b-289a-4ae1-9b5d-9f62a7decb91
-- statement:
--   Prove that choosing any $n+1$ numbers from $1,2,..,2n$ there exist $2$ , $a$ and $b$ , so that $a|b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78452 (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A.card = n + 1) (hA2 : ∀ a ∈ A, 0 < a ∧ a ≤ 2 * n) : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ∣ b   :=  by sorry
