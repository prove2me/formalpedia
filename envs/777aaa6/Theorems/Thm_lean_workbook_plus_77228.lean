-- Prove2me | Theorems.Thm_lean_workbook_plus_77228
-- name    : lean_workbook_plus_77228
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a6241420-c1a6-4230-b305-482b09b15d93
-- statement:
--   Prove the formula for the sum of squares: $1^2 + 2^2 + 3^2 + \ldots + m^2 = \frac{m(2m+1)(m+1)}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77228 (m : ℕ) :
  ∑ i in Finset.range (m+1), i^2 = m * (2 * m + 1) * (m + 1) / 6   :=  by sorry
