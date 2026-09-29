-- Prove2me | Theorems.Thm_lean_workbook_plus_7314
-- name    : lean_workbook_plus_7314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b691943e-39f9-405d-9ca5-1f20c9fa7778
-- statement:
--   Let $x,y>0 ,x^3+y^3=x-y$ and $x^2+4y^2<1.$ $$x^2+5y^2 > 4xy$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7314 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x^3 + y^3 = x - y) (h : x^2 + 4*y^2 < 1) : x^2 + 5*y^2 > 4*x*y   :=  by sorry
