-- Prove2me | Theorems.Thm_lean_workbook_plus_65711
-- name    : lean_workbook_plus_65711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/eb90d3aa-e202-4877-a289-7cc16604942d
-- statement:
--   Let $ a,b,c$ be positive numbers such that: $ a + b + c = 1$ .Prove that $ 4\left(\frac {a^2}{bc} + \frac {b^2}{ca} + \frac {c^2}{ab}\right) + 729abc\geq39$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 4 * (a^2 / b / c + b^2 / c / a + c^2 / a / b) + 729 * a * b * c ≥ 39   :=  by sorry
