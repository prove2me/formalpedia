-- Prove2me | Theorems.Thm_lean_workbook_plus_59744
-- name    : lean_workbook_plus_59744
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9baa0aac-e0bb-4c1f-b905-6786a751f95d
-- statement:
--   And so infinitely many solutions : $(a_1,b_1,c_1)=(5,2,1)$ and $(a_{n+1},b_{n+1},c_{n+1})=(17a_n+24b_n+70,12a_n+17b_n+48,1)$ : $(a_1,b_1,c_1)=(5,2,1)$\n$(a_2,b_2,c_2)=(203,142,1)$\n$(a_3,b_3,c_3)=(6929,4898,1)$\n$(a_4,b_4,c_4)=(235415,166462,1)$\n...
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59744 (a b c : ℕ → ℕ) (h₀ : a 1 = 5 ∧ b 1 = 2 ∧ c 1 = 1) (h₁ : a (n + 1) = 17 * a n + 24 * b n + 70 ∧ b (n + 1) = 12 * a n + 17 * b n + 48 ∧ c (n + 1) = 1) : ∃ n, a n = 5 ∧ b n = 2 ∧ c n = 1   :=  by sorry
