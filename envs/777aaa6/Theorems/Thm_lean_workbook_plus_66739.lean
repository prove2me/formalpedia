-- Prove2me | Theorems.Thm_lean_workbook_plus_66739
-- name    : lean_workbook_plus_66739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/22cd2a8c-b405-4888-b6a2-be1642e648bb
-- statement:
--   Prove that when $n+1$ elements are chosen from $\{1,2,\dots,2n\}$, there exist $a,b$ such that $a|b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66739 (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A.card = n + 1) (hA' : ∀ a ∈ A, 0 < a ∧ a ≤ 2 * n) : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ∣ b   :=  by sorry
