-- Prove2me | Theorems.Thm_lean_workbook_plus_23171
-- name    : lean_workbook_plus_23171
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f5a39e67-e5ba-4482-b9c8-6c1dcf4415ba
-- statement:
--   Relative error equals $ \frac{\text{error}}{\text{measurement}}$ . Since $ \frac{.02}{10}=\frac{.2}{100}$ , the relative errors are the same, or $ \boxed{\textbf{(B)}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23171 :
  abs ((0.2 : ℝ) / 100) = abs ((0.02 : ℝ) / 10)   :=  by sorry
