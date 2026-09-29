-- Prove2me | Theorems.Thm_lean_workbook_plus_22403
-- name    : lean_workbook_plus_22403
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2c69dd67-2e11-48f1-a673-766ff312d2f3
-- statement:
--   We can just write this as a summation, $\sum_{x=0}^{12} 25-2x$ and this simplifies to the arithmetic series 1+3+5+\dots+25 which is equal to 169.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22403 :
  ∑ k in (Finset.range 13), (25 - 2 * k) = 169   :=  by sorry
