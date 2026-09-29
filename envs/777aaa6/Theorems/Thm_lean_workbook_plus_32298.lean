-- Prove2me | Theorems.Thm_lean_workbook_plus_32298
-- name    : lean_workbook_plus_32298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6551508d-18f1-4016-b947-5e1d3ad3c3c4
-- statement:
--   Find an SOS expression for the function $f(a, b, c) = 3(a^2 + b^2 + c^2 + a^2b + b^2c + c^2a - 2ab - 2bc - 2ca) - (ab + bc + ca + abc - 4)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32298 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 2 * a * b - 2 * b * c - 2 * c * a) - (a * b + b * c + c * a + a * b * c - 4) = 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a - 2 * a * b - 2 * b * c - 2 * c * a) - (a * b + b * c + c * a + a * b * c - 4)   :=  by sorry
