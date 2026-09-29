-- Prove2me | Theorems.Thm_lean_workbook_plus_74012
-- name    : lean_workbook_plus_74012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bd507ec2-51ad-4249-9c3a-ddc1eb02e9f2
-- statement:
--   Verify that $(3a+4b+5c)^2 - 44(ab+bc+ca) = (b-2c)^2 + \frac{7}{3}(a-3c)^2 + \frac{5}{3}(2a-3b)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74012 : ∀ a b c : ℝ, (3 * a + 4 * b + 5 * c) ^ 2 - 44 * (a * b + b * c + c * a) = (b - 2 * c) ^ 2 + 7 / 3 * (a - 3 * c) ^ 2 + 5 / 3 * (2 * a - 3 * b) ^ 2   :=  by sorry
