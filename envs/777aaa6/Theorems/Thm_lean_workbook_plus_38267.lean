-- Prove2me | Theorems.Thm_lean_workbook_plus_38267
-- name    : lean_workbook_plus_38267
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8f2c7d9d-d914-4d5f-85dd-8eda1f51e212
-- statement:
--   Prove that $a^3+b^3+c^3-3abc = \frac{1}{2}(a+b+c)((a-b)^2+(b-c)^2+(c-a)^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38267 (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = 1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2)   :=  by sorry
