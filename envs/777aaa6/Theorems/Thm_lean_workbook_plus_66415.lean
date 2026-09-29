-- Prove2me | Theorems.Thm_lean_workbook_plus_66415
-- name    : lean_workbook_plus_66415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/015c95e0-3c32-47e2-b814-fdecd5d8dc7d
-- statement:
--   Let $ x$ and $ y$ be positive real numbers with $ x^3 + y^3 = x - y.$ Prove that $ 4x^2 -5y^2 < 5.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66415 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 = x - y) : 4 * x^2 - 5 * y^2 < 5   :=  by sorry
