-- Prove2me | Theorems.Thm_lean_workbook_plus_66143
-- name    : lean_workbook_plus_66143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7e49d6aa-8138-4366-b1e8-73166699dd0a
-- statement:
--   Let $x,y$ be reals such that $ x^2- 4xy-y^2=5.$ Prove that $2x^2+3y^2\geq 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66143 (x y : ℝ) (h : x^2 - 4*x*y - y^2 = 5) :
  2*x^2 + 3*y^2 ≥ 5   :=  by sorry
