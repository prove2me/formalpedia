-- Prove2me | Theorems.Thm_lean_workbook_plus_60638
-- name    : lean_workbook_plus_60638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/07b43b4e-a016-479d-a8cf-712954acf62a
-- statement:
--   Let $ x = 2004.5 $ . Hence the numerator is $ 6\\left(\\left(x - \\frac{3}{2}\\right)^2 + \\left(x - \\frac{1}{2}\\right)^2 + \\left(x + \\frac{1}{2}\\right)^2 + \\left(x + \\frac{3}{2}\\right)^2 + 4x\\right) = 6\\left(4x^2 + 4x + 5\\right) $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60638  (x : ℝ)
  (h₀ : x = 2004.5) :
  6 * ((x - 3 / 2)^2 + (x - 1 / 2)^2 + (x + 1 / 2)^2 + (x + 3 / 2)^2 + 4 * x) = 6 * (4 * x^2 + 4 * x + 5)   :=  by sorry
