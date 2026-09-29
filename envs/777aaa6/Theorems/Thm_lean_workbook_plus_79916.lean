-- Prove2me | Theorems.Thm_lean_workbook_plus_79916
-- name    : lean_workbook_plus_79916
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/97b4a059-a33a-4622-9b5e-4230fa843fe2
-- statement:
--   Show that the series $ \sum_{n=1}^{\infty}\frac{1}{n^2}$ converges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79916 : ∀ N : ℕ, ∃ M : ℝ, ∀ n : ℕ, n ≥ N → M ≤ ∑ i in Finset.range n, (1 : ℝ) / i ^ 2   :=  by sorry
