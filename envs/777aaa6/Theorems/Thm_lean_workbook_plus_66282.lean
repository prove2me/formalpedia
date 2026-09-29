-- Prove2me | Theorems.Thm_lean_workbook_plus_66282
-- name    : lean_workbook_plus_66282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a0523769-5382-4b4d-8793-cfc8f6457ee9
-- statement:
--   Let $x,y\geq 0$ and $2x+y^2=y^3+y+1.$ Prove that $2y+x^2\leq x^3+x+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66282 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 2 * x + y ^ 2 = y ^ 3 + y + 1) : 2 * y + x ^ 2 ≤ x ^ 3 + x + 1   :=  by sorry
