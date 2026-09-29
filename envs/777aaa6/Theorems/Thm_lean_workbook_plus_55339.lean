-- Prove2me | Theorems.Thm_lean_workbook_plus_55339
-- name    : lean_workbook_plus_55339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/193e6056-e0eb-47bd-995d-a9d8f6f0e8dc
-- statement:
--   Let $n$ be Positive integer,prove that $\frac{1}{2}<\left(1+\frac{1}{3}\right)\left(1+\frac{1}{3^2}\right)\cdots\left(1+\frac{1}{3^n}\right)<2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55339 : ∀ n : ℕ, (1 / 2 : ℝ) < ∏ i in Finset.range (n + 1), (1 + 1 / (3 ^ i)) ∧ ∏ i in Finset.range (n + 1), (1 + 1 / (3 ^ i)) < 2   :=  by sorry
