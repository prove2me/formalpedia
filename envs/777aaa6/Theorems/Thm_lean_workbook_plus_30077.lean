-- Prove2me | Theorems.Thm_lean_workbook_plus_30077
-- name    : lean_workbook_plus_30077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/af55f44f-d07b-4584-9e35-166bd6ac17f7
-- statement:
--   Let $x$ be the amount of money the original movie grossed. Then $2x + 114 = 1542.$ From this we see that $2x = 1428,$ so $x = 714.$ Hence, the original movie grossed $\$714$ million, while the sequel grossed $\$828$ million.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30077  (x : ℝ)
  (h₀ : 2 * x + 114 = 1542) :
  x = 714 ∧ 2 * x + 114 = 1542   :=  by sorry
