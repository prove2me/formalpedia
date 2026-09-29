-- Prove2me | Theorems.Thm_lean_workbook_plus_58382
-- name    : lean_workbook_plus_58382
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/167b1d60-3a19-4b76-8284-94fef7286422
-- statement:
--   Compute the greatest value of $ x + y$ for integers $ x,y$ , such that $ x^2 + y^2 = 884$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58382 (x y : ℤ) (h : x^2 + y^2 = 884) : x + y ≤ 42   :=  by sorry
