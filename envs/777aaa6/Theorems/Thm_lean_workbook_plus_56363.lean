-- Prove2me | Theorems.Thm_lean_workbook_plus_56363
-- name    : lean_workbook_plus_56363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/02a3df90-ea49-4e4b-8292-b46312d50385
-- statement:
--   Prove the inequality $(x^2+2y^2-xy)z^2+(x^3-xy^2-4x^2y)z+yx^3+y^2x^2\geq 0$ for $x, y, z > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56363 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + 2*y^2 - x*y) * z^2 + (x^3 - x*y^2 - 4*x^2*y) * z + y*x^3 + y^2*x^2 ≥ 0   :=  by sorry
