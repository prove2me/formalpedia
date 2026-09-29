-- Prove2me | Theorems.Thm_lean_workbook_plus_38505
-- name    : lean_workbook_plus_38505
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e0ad995b-c21d-4c88-8e64-8721632dfecc
-- statement:
--   for $ x>0$ we have $ 9x^6+(x^4+x^2+1)^2-18x^5=(x-1)^2(x^6+2x^5+14x^4+8x^3+5x^2+2x+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38505 (x : ℝ) (hx : x > 0) : 9 * x ^ 6 + (x ^ 4 + x ^ 2 + 1) ^ 2 - 18 * x ^ 5 = (x - 1) ^ 2 * (x ^ 6 + 2 * x ^ 5 + 14 * x ^ 4 + 8 * x ^ 3 + 5 * x ^ 2 + 2 * x + 1)   :=  by sorry
