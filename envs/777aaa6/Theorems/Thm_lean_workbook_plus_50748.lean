-- Prove2me | Theorems.Thm_lean_workbook_plus_50748
-- name    : lean_workbook_plus_50748
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c777c1c9-4c5b-48b3-812a-20d22a800e49
-- statement:
--   We have $x_1+x_2+\cdots +x_n\geq y_i\geq x_i^2 \Rightarrow x_i^2 y_i \leq y_i^2 \leq (x_1+x_2+\cdots+x_n)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50748 (n : ℕ) (x y : ℕ → ℕ) (h₁ : ∑ i in Finset.range n, x i ≥ y i) (h₂ : y i ≥ x i ^ 2) : x i ^ 2 * y i ≤ y i ^ 2 ∧ y i ^ 2 ≤ (∑ i in Finset.range n, x i) ^ 2   :=  by sorry
