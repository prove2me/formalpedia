-- Prove2me | Theorems.Thm_lean_workbook_plus_55813
-- name    : lean_workbook_plus_55813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/69e12516-2e5a-4fd8-83a6-2fd1a970dcce
-- statement:
--   $(x^4-4x^3+8x+4)=x^4-4x^3-4x^2+4x^2+8x+4=(x^4-2x^3-2x^2)+(-2x^3+4x^2+4x)+(-2x^2+4x+4)=x^2(x^2-2x-2)-2x(x^2-2x-2)-2(x^2-2x-2)=(x^2-2x-2)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55813  (x : ℝ) :
  x^4 - 4 * x^3 + 8 * x + 4 = (x^2 - 2 * x - 2)^2   :=  by sorry
