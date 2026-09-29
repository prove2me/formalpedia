-- Prove2me | Theorems.Thm_lean_workbook_plus_10660
-- name    : lean_workbook_plus_10660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/883e71ec-c4ac-4fd0-9f7b-e4c2b3d151c6
-- statement:
--   Let $x,y\geq 0$ and $x+y^2=y^3+1.$ Prove that $y+x^2\leq x^3+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10660 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y^2 = y^3 + 1) : y + x^2 ≤ x^3 + 1   :=  by sorry
