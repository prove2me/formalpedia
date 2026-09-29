-- Prove2me | Theorems.Thm_lean_workbook_plus_71067
-- name    : lean_workbook_plus_71067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/eaf3d8e8-841b-4231-a3d2-bbd819eb249c
-- statement:
--   Let $x,y$ be reals such that $ x^2- 4xy-y^2=5.$ Prove that $3x^2+y^2\geq 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71067 (x y : ℝ) (h : x^2 - 4*x*y - y^2 = 5) : 3*x^2 + y^2 ≥ 5   :=  by sorry
