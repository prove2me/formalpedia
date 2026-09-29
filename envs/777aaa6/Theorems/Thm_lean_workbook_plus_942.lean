-- Prove2me | Theorems.Thm_lean_workbook_plus_942
-- name    : lean_workbook_plus_942
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e3a29989-597b-43c3-85f4-51af148d08d1
-- statement:
--   Let $x,y$ be reals such that $x^2+y^2\leq 2x+y .$ Prove that $2x+y\leq 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_942 (x y : ℝ) (h : x^2 + y^2 ≤ 2 * x + y) : 2 * x + y ≤ 5   :=  by sorry
