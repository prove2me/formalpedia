-- Prove2me | Theorems.Thm_lean_workbook_plus_2128
-- name    : lean_workbook_plus_2128
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7ba48f04-c6b1-4e54-af00-9fa0dccc778f
-- statement:
--   Prove by induction that $\sum_{i=1}^{n}i^4=1/30\,n \left( 2\,n+1 \right) \left( n+1 \right) \left( 3\,{n}^{2}+3\,n-1 \right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2128 : ∀ n : ℕ, ∑ i in Finset.range (n+1), i^4 = 1/30 * n * (2 * n + 1) * (n + 1) * (3 * n^2 + 3 * n - 1)   :=  by sorry
