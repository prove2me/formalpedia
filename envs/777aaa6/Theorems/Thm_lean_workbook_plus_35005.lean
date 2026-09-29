-- Prove2me | Theorems.Thm_lean_workbook_plus_35005
-- name    : lean_workbook_plus_35005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/44dde926-ee47-4916-9ad4-65371275b0b1
-- statement:
--   Given that $(x, y)$ satisfies $x^2+y^2=9$ , what is the largest possible value of $x^2 + 3y^2 + 4x$ ? (For this problem I solved for $y$ in the first equation and plugged it back in the second to get 29. What other way can this be done?)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35005 (x y : ℝ) (hx : x^2 + y^2 = 9) : x^2 + 3*y^2 + 4*x ≤ 29   :=  by sorry
