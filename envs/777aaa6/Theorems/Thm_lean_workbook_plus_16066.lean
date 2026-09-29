-- Prove2me | Theorems.Thm_lean_workbook_plus_16066
-- name    : lean_workbook_plus_16066
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2bc7be9d-8c8d-4ccc-b5bd-cae1ebf14ae7
-- statement:
--   Your sum $ =\frac{b-a}{n} \sum_{k=1}^n \left(a+ \frac{k(b-a)}{n}\right)^2 - \frac{b-a}{n} \sum_{k=1}^n \left(a+\frac{b-a}{n} \right)\left(a+ \frac{k(b-a)}{n}\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16066 : ∀ a b : ℝ, ∀ n : ℕ, (∑ k in Finset.Icc 1 n, (a + k * (b - a) / n)^2) - (∑ k in Finset.Icc 1 n, (a + (b - a) / n) * (a + k * (b - a) / n)) = (b - a) / n * (∑ k in Finset.Icc 1 n, (a + k * (b - a) / n)^2 - ∑ k in Finset.Icc 1 n, (a + (b - a) / n) * (a + k * (b - a) / n))   :=  by sorry
