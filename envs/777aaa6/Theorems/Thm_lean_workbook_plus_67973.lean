-- Prove2me | Theorems.Thm_lean_workbook_plus_67973
-- name    : lean_workbook_plus_67973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/44721407-7e24-4049-b828-22081bae5d95
-- statement:
--   $ \frac{n^2+7}{n^2+4}=\frac{n^2+4+3}{n^2+4}=1+\frac{3}{n^2+4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67973  (n : ℝ) :
  (n^2 + 7) / (n^2 + 4) = 1 + 3 / (n^2 + 4)   :=  by sorry
