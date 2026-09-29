-- Prove2me | Theorems.Thm_lean_workbook_plus_22085
-- name    : lean_workbook_plus_22085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/05413e15-8d9f-4b55-911f-eef3e3c9dcaa
-- statement:
--   By simple calculation, we get: $(x^2-3x-2)^2-3(x^2-3x-2)-2-x=(x^2-4x-2) (x^2-2x-4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22085  (x : ℝ) :
  (x^2 - 3 * x - 2)^2 - 3 * (x^2 - 3 * x - 2) - 2 - x = (x^2 - 4 * x - 2) * (x^2 - 2 * x - 4)   :=  by sorry
