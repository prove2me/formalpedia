-- Prove2me | Theorems.Thm_lean_workbook_plus_80039
-- name    : lean_workbook_plus_80039
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/4f57396b-33da-44db-b7c5-197daafe4d57
-- statement:
--   Writing $\sin^{2}A=1-\cos^{2}A$ etc. and using the formula $\cos^{2}A+\cos^{2}B+\cos^{2}C+2\cos A\cos B\cos C=1$ it is equivalent to $2\cos A\cos B+2\cos B\cos C+2\cos C\cos A-4\cos A\cos B\cos C\leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80039 :
  ∀ A B C : ℝ,
    2 * Real.cos A * Real.cos B + 2 * Real.cos B * Real.cos C + 2 * Real.cos C * Real.cos A -
      4 * Real.cos A * Real.cos B * Real.cos C ≤ 1   :=  by sorry
