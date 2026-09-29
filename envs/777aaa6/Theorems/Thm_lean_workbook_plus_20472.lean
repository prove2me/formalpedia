-- Prove2me | Theorems.Thm_lean_workbook_plus_20472
-- name    : lean_workbook_plus_20472
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/51e443fb-9283-4b79-970d-d9c9ad37f7e9
-- statement:
--   Prove that there exist two infinite sequences $(A_n)_{n\ge1}$ and $(B_n)_{n\ge1}$ of positive integers such that the following conditions hold simultaneously:\n\n(i) $1 < a_1 < a_2 < a_3 < \ldots$\n\n(ii) $a_n < b_n < a_n^2$, for all $n \ge 1$\n\n(iii) $a_n - 1$ divides $b_n - 1$, for all $n \ge 1$\n\n(iv) $(a_n)^2 - 1$ divides $(b_n)^2 - 1$, for all $n \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20472 : ∃ a b : ℕ → ℕ, (∀ n, 1 < a n ∧ a n < b n ∧ a n^2 < b n^2) ∧ (∀ n, (a n - 1) ∣ (b n - 1)) ∧ (∀ n, (a n^2 - 1) ∣ (b n^2 - 1))   :=  by sorry
