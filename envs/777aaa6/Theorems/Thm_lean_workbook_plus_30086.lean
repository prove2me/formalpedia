-- Prove2me | Theorems.Thm_lean_workbook_plus_30086
-- name    : lean_workbook_plus_30086
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/1a5bd580-b416-46d0-affd-e6e0cd268874
-- statement:
--   Sigma is for sum. Specifically @2above meant $\sum_{i=1}^5 (x_i - \overline{x})^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30086 (x : ℕ → ℝ) (n : ℕ) (h₁ : n = 5) :
  ∑ i in Finset.range n, (x i - (∑ j in Finset.range n, x j)/n)^2 =
    ∑ i in Finset.range 5, (x i - (∑ j in Finset.range 5, x j)/5)^2   :=  by sorry
