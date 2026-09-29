-- Prove2me | Theorems.Thm_lean_workbook_plus_57818
-- name    : lean_workbook_plus_57818
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b39e3b6c-46c5-44cc-9a56-4175ed0ad693
-- statement:
--   Given a subset $S$ of $\left\{1,2,3,...,2n\right\}$ with $n+1$ elements, prove that there exist $a, b \in S$ such that $a | b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57818 (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (2 * n)) (hS' : S.card = n + 1) : ∃ a b, a ∈ S ∧ b ∈ S ∧ a ∣ b   :=  by sorry
