-- Prove2me | Theorems.Thm_lean_workbook_plus_44588
-- name    : lean_workbook_plus_44588
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7db4aad0-6e05-4ba5-872c-788d3318662e
-- statement:
--   Show that the series \(\sum_2^\infty \frac{1}{n(\ln n)^{3/2}}\) converges using the Integral Criterion.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44588 : ∀ n : ℕ, n ≥ 2 → 0 ≤ 1 / (n * (Real.log n)^(3/2)) ∧ ∀ n : ℕ, n ≥ 2 → 1 / (n * (Real.log n)^(3/2)) ≤ 1 / ((n:ℝ) * (Real.log n)^(3/2))  :=  by sorry
