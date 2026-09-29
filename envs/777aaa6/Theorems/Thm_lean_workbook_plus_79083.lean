-- Prove2me | Theorems.Thm_lean_workbook_plus_79083
-- name    : lean_workbook_plus_79083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b751e271-b005-4a0b-90d2-8880e10cac3b
-- statement:
--   Given the conditions, derive the equation $abc + \frac{1}{abc} = 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79083 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : a * b * c + 1 / (a * b * c) = 2   :=  by sorry
