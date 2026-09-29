-- Prove2me | Theorems.Thm_lean_workbook_plus_50714
-- name    : lean_workbook_plus_50714
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/34e71475-80f5-497b-811f-969b998c1879
-- statement:
--   Prove that $1+\frac{1}{2}+\frac{1}{3}+...+\frac{1}{n}<n\left(1-\frac{1}{\sqrt[n]{n}}+1\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50714 : ∀ n : ℕ, (∑ i in Finset.Icc 1 n, (1 / i)) < n * (1 - 1 / (n:ℝ)^(1 / n) + 1)   :=  by sorry
