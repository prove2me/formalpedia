-- Prove2me | Theorems.Thm_lean_workbook_plus_1723
-- name    : lean_workbook_plus_1723
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/42513889-9c90-4173-90c4-0512b8f95bac
-- statement:
--   $\sum_{i=1}^n x_iz_i\le\sum_{i=1}^n x_iy_i$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1723 (n : ℕ) (x y z : ℕ → ℕ) (h₁ : ∀ i, 0 < x i ∧ 0 < y i ∧ 0 < z i) (h₂ : ∀ i, z i < y i) : ∑ i in Finset.range n, x i * z i ≤ ∑ i in Finset.range n, x i * y i   :=  by sorry
