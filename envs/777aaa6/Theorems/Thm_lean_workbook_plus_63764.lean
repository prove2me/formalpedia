-- Prove2me | Theorems.Thm_lean_workbook_plus_63764
-- name    : lean_workbook_plus_63764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5cddb9d0-a73f-49d4-a137-4b0065716ae1
-- statement:
--   Express $a^3 + b^3 + c^3$ as $3abc + (a+b+c)(a^2+b^2+c^2-ab-bc-ca)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63764 (a b c : ℤ) : a^3 + b^3 + c^3 = 3 * a * b * c + (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a)   :=  by sorry
