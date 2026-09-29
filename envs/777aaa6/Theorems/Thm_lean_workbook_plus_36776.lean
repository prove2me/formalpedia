-- Prove2me | Theorems.Thm_lean_workbook_plus_36776
-- name    : lean_workbook_plus_36776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7f3aee5f-4dcc-4a7d-876a-c51c29bc9d5a
-- statement:
--   $a-b = \frac{(3x^2 + 7xy + 2y^2)-(2x^2 + 7xy + 3y^2)}{(2x+y)(3x+y)} = \frac{x^2 - y^2}{(2x+y)(3x+y)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36776 (x y a b : ℝ) : a - b = (3 * x ^ 2 + 7 * x * y + 2 * y ^ 2 - (2 * x ^ 2 + 7 * x * y + 3 * y ^ 2)) / ((2 * x + y) * (3 * x + y)) → a - b = (x ^ 2 - y ^ 2) / ((2 * x + y) * (3 * x + y))   :=  by sorry
