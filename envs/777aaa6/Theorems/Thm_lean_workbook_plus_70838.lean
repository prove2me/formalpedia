-- Prove2me | Theorems.Thm_lean_workbook_plus_70838
-- name    : lean_workbook_plus_70838
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/da86179e-446c-475a-ad68-d612f01b7df3
-- statement:
--   Factor $\frac{2}{n(n+1)}$ into $2(\frac{1}{n}-\frac{1}{n+1})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70838 ∀ n : ℕ, (↑2 / (n * (n + 1) : ℕ)) = (2 * (1 / n - 1 / (n + 1) : ℚ))   :=  by sorry
