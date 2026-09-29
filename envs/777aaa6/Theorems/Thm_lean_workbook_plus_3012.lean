-- Prove2me | Theorems.Thm_lean_workbook_plus_3012
-- name    : lean_workbook_plus_3012
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ce0715dd-9738-46b4-842a-b8d6ea732b02
-- statement:
--   Replace 19 with m and replace 200 with n, and the problem holds as long as m <= n. That is, given $x_1, \dots, x_m \in [1,n]$ and $y_1, \dots, y_n \in [1,m]$ and $\sum x_i < \sum y_i$ then there exists a sub-sum of $x_i$ that is equal to a sub-sum of $y_i$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3012 (m n : ℕ) (x : Fin m → ℕ) (y : Fin n → ℕ) (h₁ : m ≤ n) (h₂ : ∑ i, x i < ∑ j, y j) : ∃ A B, A ⊆ Finset.univ ∧ B ⊆ Finset.univ ∧ ∑ i in A, x i = ∑ j in B, y j   :=  by sorry
