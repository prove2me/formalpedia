-- Prove2me | Theorems.Thm_lean_workbook_plus_9744
-- name    : lean_workbook_plus_9744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ace304cf-7840-426f-ac28-617f59dfa696
-- statement:
--   Given 16 distinct positive integers not exceeding 100, prove that it is possible to choose 4 distinct integers $ a$ , $ b$ , $ c$ and $ d$ such that $ a+c = b + d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9744 (A : Finset ℕ) (hA : A.card = 16) (hA' : ∀ a ∈ A, a ≤ 100) : ∃ a b c d : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧ a + c = b + d   :=  by sorry
