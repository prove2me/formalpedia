-- Prove2me | Theorems.Thm_lean_workbook_plus_69946
-- name    : lean_workbook_plus_69946
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/94edee56-75b4-434f-89e8-e35c8b92373f
-- statement:
--   Case (ii): If $1>x\ge0$ , our equation is $x(1-x)-4x+3=x-x^2-4x+3=-x^2-3x+3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69946 ∀ x, 1 > x ∧ x >= 0 → x - x^2 - 4 * x + 3 = -x^2 - 3 * x + 3   :=  by sorry
