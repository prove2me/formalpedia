-- Prove2me | Theorems.Thm_lean_workbook_plus_77370
-- name    : lean_workbook_plus_77370
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7fe0914e-6409-4a65-ba01-a018b4ae583c
-- statement:
--   4) $ \frac{1}{2}\leq\frac{1}{n+1}+\frac{1}{n+2}+....+\frac{1}{2n}\leq\frac{3}{4} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77370 : ∀ n : ℕ, ∑ k in Finset.Icc (1 : ℕ) n, (1 : ℝ) / (k + 1) ≤ 3 / 4 ∧ 1 / 2 ≤ ∑ k in Finset.Icc (1 : ℕ) n, (1 : ℝ) / (k + 1)   :=  by sorry
