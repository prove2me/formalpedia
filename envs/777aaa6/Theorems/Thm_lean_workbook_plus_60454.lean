-- Prove2me | Theorems.Thm_lean_workbook_plus_60454
-- name    : lean_workbook_plus_60454
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3c45f94b-5e90-4887-add4-d646f04617a4
-- statement:
--   Solve the equation $10\,{\frac {\tan \left( 1/2\,x \right) }{1+ \left( \tan \left( 1/2\,x \right) \right) ^{2}}}-3\,{\frac {1- \left( \tan \left( 1/2\,x \right) \right) ^{2}}{1+ \left( \tan \left( 1/2\,x \right) \right) ^{2}}}-3 = 0$ for $t = \tan \frac{1}{2} x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60454 (t : ℝ) (x : ℝ) (h₁ : t = Real.tan (x / 2)) : (10 * t / (1 + t^2) - 3 * (1 - t^2) / (1 + t^2) - 3 = 0) ↔ t = 3 / 5   :=  by sorry
