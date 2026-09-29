-- Prove2me | Theorems.Thm_lean_workbook_plus_3408
-- name    : lean_workbook_plus_3408
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4fac0859-8e46-43e7-94ac-8ac128087b77
-- statement:
--   For any $ a,b,c$ the following identity is true: $(a + b - c)\,(a - b + c) = \frac {1}{4}\left(\,6\,(ab + ac + bc) - 5\,(a^2 + b^2 + c^2) + (b + c - 3\,a)^2\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3408 (a b c : ℝ) : (a + b - c) * (a - b + c) = 1 / 4 * (6 * (a * b + a * c + b * c) - 5 * (a ^ 2 + b ^ 2 + c ^ 2) + (b + c - 3 * a) ^ 2)   :=  by sorry
