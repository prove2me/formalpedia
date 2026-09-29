-- Prove2me | Theorems.Thm_lean_workbook_plus_44488
-- name    : lean_workbook_plus_44488
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c4b8bade-f789-4a3a-8c28-1e08fd7018d4
-- statement:
--   Determine the convergence of the series $ \sum_{n=2}^{\infty}\frac{1}{(\log n)^{\log n}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44488 : ∀ n : ℕ, n ≥ 2 → 0 < 1 / (Real.log n) ^ (Real.log n)   :=  by sorry
